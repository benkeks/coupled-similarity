package de.bbisping.coupledsim.flink

import org.apache.flink.api.scala._
import org.apache.flink.api.scala.DataSet
import org.apache.flink.graph.scala.Graph
import org.apache.flink.types.NullValue
import de.bbisping.coupledsim.util.Coloring
import org.apache.flink.api.common.functions.FlatMapFunction
import org.apache.flink.util.Collector
import org.apache.flink.api.common.functions.FilterFunction
import org.apache.flink.api.common.functions.JoinFunction
import scala.reflect.ClassTag
import org.apache.flink.api.common.typeinfo.TypeInformation


/**
 * A variant of the coupled simulation game computation enhanced with a gradual
 * discovery of the game space.
 */
class CoupledSimulationGameDiscovery {
  
  import CoupledSimulationFlink.Action
  import CoupledSimulationGame._
  
  type Signature = Set[(Coloring.Color, Coloring.Color)]
  
  // due to some strange behavior of flink, we unfortunately cannot use these type synonyms
  type GameNode = (Action, Int, Int)
  type GameMove = ((Action, Int, Int), (Action, Int, Int))
  
  def compute(
      ts: Graph[Int, NullValue, CoupledSimulationFlink.Action],
      signaturesOpt: Option[DataSet[(Int, Set[(Coloring.Color, Coloring.Color)])]],
      TAU: CoupledSimulationFlink.Action,
      env: ExecutionEnvironment)
  : (DataSet[(CoupledSimulationFlink.Action, Int, Int)],
     DataSet[((CoupledSimulationFlink.Action, Int, Int), (CoupledSimulationFlink.Action, Int, Int))]) = {
    
    val possibleAttackerNodes: DataSet[(Action, Int, Int)] =
      (ts.getVertexIds cross ts.getVertexIds) {
        (p, q) => (ATTACK, p, q)
    }
    
    val attackerNodes: DataSet[(Action, Int, Int)] = signaturesOpt match {
      case Some(signatures) =>
        // only generate attacker nodes where there is a chance of the defender winning
        (signatures cross signatures) flatMap new FlatMapFunction[((Int, Signature), (Int, Signature)), (Action, Int, Int)] {
          def flatMap(pqSig: ((Int, Signature), (Int, Signature)),
              out: Collector[(Action, Int, Int)]) = pqSig match {
            case ((p, pSig), (q, qSig)) =>
              if (pSig.size <= qSig.size && (pSig subsetOf qSig)) {
                out.collect((ATTACK, p, q))
              }
          }
        }
      case None =>
        possibleAttackerNodes
    }
    
    // only allow "real" (non-stuttering) tau-steps (because otherwise this could be used
    // by the defender to go into infinite loops and win) (we assume that tau cycles have been compressed)
    val tauSteps = ts.getEdgesAsTuple3() filter new FilterFunction[((Int, Int, Action))] {
      def filter(edge: ((Int, Int, Action))) = edge match {
        case ((p0, p1, a)) => a == TAU && p0 != p1
      }
    }
    
    val initialAttacks: DataSet[((Action, Int, Int), (Action, Int, Int))] = attackerNodes.map(a => (a, a))
    
    val gameMoves: DataSet[((Action, Int, Int), (Action, Int, Int))] = initialAttacks.
      iterateDelta(initialAttacks, CoupledSimulationFlink.MAX_ITERATIONS, Array(0,1)) { (discoveredMoves: DataSet[((Action, Int, Int), (Action, Int, Int))], deltaMoves: DataSet[((Action, Int, Int), (Action, Int, Int))]) =>
        val deltaNodes: DataSet[(Action, Int, Int)] = deltaMoves.map(_._2).distinct
        
        val newAttackerNodes: DataSet[(Action, Int, Int)] = deltaNodes.filter(_._1 == ATTACK)
        val newSimulationChallenges: DataSet[((Action, Int, Int), (Action, Int, Int))] =
          (ts.getEdgesAsTuple3() join newAttackerNodes)
            .where(0/*src*/).equalTo(1/*p*/) { (edge, an) =>
              (an, (edge._3/*a*/, edge._2/*tar*/, an._3 /*q*/))
        }
        
        val newDefenderSimulationNodes: DataSet[(Action, Int, Int)] = deltaNodes.filter(n => n._1 != ATTACK && n._1 != COUPLING)
        
         // the simulation answer can be postponed by internal steps on the right hand side
        val newSimulationWeakSteps: DataSet[((Action, Int, Int), (Action, Int, Int))] =
          (newDefenderSimulationNodes join tauSteps)
          .where(2/*q*/).equalTo(0/*p0*/) { (dn, edge) =>
            (dn, (dn._1, dn._2, edge._2))
        }
        
        // at some point the defender has to decide that this is the right place to perform the visible action
        val newSimulationAnswersUnfiltered =
          (newDefenderSimulationNodes join ts.getEdgesAsTuple3())
          .where(2/*q*/,0/*a*/).equalTo(0/*src*/,2/*a*/) ((dn, edge) => (dn, (ATTACK, dn._2, edge._2))) // TAU
        
        val newSimulationAnswers: DataSet[((Action, Int, Int), (Action, Int, Int))] =
          (attackerNodes join newSimulationAnswersUnfiltered).where(n => n).equalTo(1)((a, mv) => mv)
          
        // afterwards (or directly on tau challenges) the defender may yield the inititiative back to the attacker
        val newSimulationAnswerTauResolves: DataSet[((Action, Int, Int), (Action, Int, Int))] =
          (newDefenderSimulationNodes
              .filter(_._1 == TAU)
              join attackerNodes) // ??
              .where(1,2).equalTo(1,2)
          
        // every attacker node can be the entry or exit of a coupling challenge
        val newCouplingChallengesEntrys: DataSet[((Action, Int, Int), (Action, Int, Int))]  =
          (newAttackerNodes map (an => (an, (COUPLING, an._2, an._3))))
          
        val newDefenderCouplingNodes: DataSet[(Action, Int, Int)] = deltaNodes.filter(n => n._1 == COUPLING)
          
        val newCouplingChallengesExits: DataSet[((Action, Int, Int), (Action, Int, Int))] =
          (newDefenderCouplingNodes join attackerNodes).where(1,2).equalTo(2,1)// map (cn => (cn, (ATTACK, cn._3, cn._2)))) //join attackerNodes).where(1).equalTo(2)
        
        // during a coupling challenge, the defender may move with tau steps on the right-hand side.
        val newCouplingMoves: DataSet[((Action, Int, Int), (Action, Int, Int))] =
          (newDefenderCouplingNodes join tauSteps)
          .where(2/*q*/).equalTo(0/*src*/) (new JoinFunction[(Action, Int, Int), (Int, Int, Action), ((Action, Int, Int), (Action, Int, Int))] {
            def join(cn: (Action, Int, Int), edge: (Int, Int, Action)) = {
              (cn, (COUPLING, cn._2, edge._2))
            }
        })
          
        val newGameMoves = newSimulationChallenges union
          newSimulationWeakSteps union
          newSimulationAnswers union
          newSimulationAnswerTauResolves union
          newCouplingChallengesEntrys union
          newCouplingChallengesExits union
          newCouplingMoves
          
        val reallyNewGameMoves = (newGameMoves coGroup discoveredMoves)
          .where(0,1).equalTo(0,1).apply(fun = { (mv1: Iterator[((Action, Int, Int), (Action, Int, Int))], mv2: Iterator[((Action, Int, Int), (Action, Int, Int))], out: Collector[((Action, Int, Int), (Action, Int, Int))]) => 
            if (mv2.isEmpty) {
              for (nm <- mv1) out.collect(nm)
            }
        })

        (reallyNewGameMoves, reallyNewGameMoves)
    }
    
    val gameNodes = attackerNodes //union defenderSimulationNodes
      
    (gameNodes, gameMoves)
  }
  
}