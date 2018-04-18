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


class CoupledSimulationGame {
  
  import CoupledSimulationFlink.Action
  import CoupledSimulationGame._
  
  type Signature = Set[(Coloring.Color, Coloring.Color)]
  
  def compute(
      ts: Graph[Int, NullValue, CoupledSimulationFlink.Action],
      signaturesOpt: Option[DataSet[(Int, Set[(Coloring.Color, Coloring.Color)])]],
      TAU: CoupledSimulationFlink.Action)
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
    
    //println(attackerNodes.collect())
  
    val simulationChallenges: DataSet[((Action, Int, Int), (Action, Int, Int))]  =
      (ts.getEdgesAsTuple3() join possibleAttackerNodes) // ? 
      .where(0/*src*/).equalTo(1/*p*/) { (edge, an) =>
        (an, (edge._3/*a*/, edge._2/*tar*/, an._3 /*q*/))
    }
    
    val defenderSimulationNodes: DataSet[(Action, Int, Int)] =
      ((simulationChallenges flatMap new FlatMapFunction[((Action, Int, Int), (Action, Int, Int)), (Action, Int, Int)] { 
        def flatMap(simChallenge: ((Action, Int, Int), (Action, Int, Int)),
              out: Collector[(Action, Int, Int)]) = simChallenge match {
          case ((_, rhs)) =>
            out.collect(rhs)
            //out.collect((TAU, rhs._2, rhs._3))
        }
      })
      union (possibleAttackerNodes map (an => (TAU, an._2, an._3)))
      ).distinct()
      
  //        Seq(rhs, (TAU, rhs._2, rhs._3))
  //      }: (((Action, Int, Int), (Action, Int, Int))) => TraversableOnce[(Action, Int, Int)]))
  //      .distinct()
    
    // only allow "real" (non-stuttering) tau-steps (because otherwise this could be used
    // by the defender to go into infinite loops and win) (we assume that tau cycles have been compressed)
    val tauSteps = ts.getEdgesAsTuple3() filter new FilterFunction[((Int, Int, Action))] {
      def filter(edge: ((Int, Int, Action))) = edge match {
        case ((p0, p1, a)) => a == TAU && p0 != p1
      }
    }
    
    // the simulation answer can be postponed by internal steps on the right hand side
    val simulationWeakSteps: DataSet[((Action, Int, Int), (Action, Int, Int))] =
      (defenderSimulationNodes join tauSteps)
      .where(2/*q*/).equalTo(0/*p0*/) { (dn, edge) =>
        (dn, (dn._1, dn._2, edge._2))
    }
    
    // at some point the defender has to decide that this is the right place to perform the visible action
    val simulationAnswers: DataSet[((Action, Int, Int), (Action, Int, Int))] =
      (defenderSimulationNodes join ts.getEdgesAsTuple3())
      .where(2/*q*/,0/*a*/).equalTo(0/*src*/,2/*a*/) (new JoinFunction[(Action, Int, Int), (Int, Int, Action), ((Action, Int, Int), (Action, Int, Int))] {
        def join(dn: (Action, Int, Int), edge: (Int, Int, Action)) = {
          (dn, (TAU, dn._2, edge._2))
        }
      })
    
    // afterwards (or directly on tau challenges) the defender may yield the intitiative back to the attacker
    val simulationAnswerTauResolves: DataSet[((Action, Int, Int), (Action, Int, Int))] =
      (defenderSimulationNodes
          .filter(new FilterFunction[(Action, Int, Int)] {
            def filter(challenge: (Action, Int, Int)) = challenge._1 == TAU})
       join attackerNodes) // ??
      .where(1,2).equalTo(1,2)/* { dn =>
        (dn, (ATTACK, dn._2, dn._3))//TODO: Restrict this to attacker nodes which are in the over-approximation (otherwise this may generate spurious victories for the defender!!)
    }*/
    
    // every attacker node can be the entry or exit of a coupling challenge
    val couplingChallengesEntrysExits: DataSet[((Action, Int, Int), (Action, Int, Int))]  =
      (possibleAttackerNodes map (an => (an, (COUPLING, an._2, an._3)))) union // ??
      (attackerNodes map (an => ((COUPLING, an._3, an._2), an))) // ????
//      
//      attackerNodes flatMap new FlatMapFunction[(Action, Int, Int), ((Action, Int, Int), (Action, Int, Int))] {
//        def flatMap(an: (Action, Int, Int), out: Collector[((Action, Int, Int), (Action, Int, Int))]) = {
//          out.collect((an, (COUPLING, an._2, an._3)))
//          out.collect(((COUPLING, an._3, an._2), an))// note the reversed order of p and q!!!
//        }
//    }
    
    // during a coupling challenge, the defender may move with tau steps on the right-hand side.
    val couplingMoves: DataSet[((Action, Int, Int), (Action, Int, Int))] =
      (possibleAttackerNodes join tauSteps)
      .where(2/*q*/).equalTo(0/*src*/) (new JoinFunction[(Action, Int, Int), (Int, Int, Action), ((Action, Int, Int), (Action, Int, Int))] {
        def join(an: (Action, Int, Int), edge: (Int, Int, Action)) = {
          ((COUPLING, an._2, an._3), (COUPLING, an._2, edge._2))
        }
    })
    
    val gameNodes = attackerNodes union defenderSimulationNodes
    val gameMoves = simulationChallenges union
      simulationWeakSteps union simulationAnswers union simulationAnswerTauResolves union
      couplingChallengesEntrysExits union couplingMoves
      
    (gameNodes, gameMoves)
  }
//
//  def genAttack(pqWithSig: ((Int, Set[(Coloring.Color, Coloring.Color)]), (Int, Set[(Coloring.Color, Coloring.Color)]))) = pqWithSig match {
//    case ((p, pSig), (q, qSig)) =>
//      //if (pSig.size <= qSig.size && (pSig subsetOf qSig)) {
//         (ATTACK, p, q)
////      } else {
////         (ATTACK, p, q)
////      }
//  }
      
    //  (Int, Set[(Coloring.Color, Coloring.Color)]), (Int, Set[(Coloring.Color, Coloring.Color)]))) => Seq[(Action, Int, Int)]
  
  
}

object CoupledSimulationGame {
  val ATTACK: Long = -1
  val COUPLING: Long = -2
}