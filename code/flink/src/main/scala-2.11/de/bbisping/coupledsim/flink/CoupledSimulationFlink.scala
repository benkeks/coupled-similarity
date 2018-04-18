package de.bbisping.coupledsim.flink

import org.apache.flink.api.scala._
import org.apache.flink.graph.scala.Graph
import org.apache.flink.types.NullValue
import org.apache.flink.api.common.typeinfo.TypeInformation
import org.apache.flink.core.fs.FileSystem
import org.apache.flink.api.common.functions._
import org.apache.flink.types.LongValue
import org.apache.flink.graph.spargel.ScatterFunction
import org.apache.flink.graph.spargel.MessageIterator
import org.apache.flink.graph.spargel.GatherFunction
import org.apache.flink.graph.Vertex
import org.apache.flink.graph.Edge
import scala.reflect.ClassTag
import org.apache.flink.graph.spargel.ScatterGatherConfiguration
import org.apache.flink.graph.EdgeDirection
import org.apache.flink.api.java.utils.ParameterTool
import org.apache.flink.api.scala.utils.`package`.DataSetUtils
import org.apache.flink.graph.asm.translate.TranslateFunction
import org.apache.flink.api.scala.ClosureCleaner

import de.bbisping.coupledsim.ts.WeakTransitionSystem
import de.bbisping.coupledsim.util.LabeledRelation
import de.bbisping.coupledsim.util.Coloring
import de.bbisping.coupledsim.util.Relation
import org.apache.flink.util.Collector

/**
 * Computes the coupled simulation preorder using a game-theoretic algorithm.
 * 
 * 
 *   The program takes the following arguments:
 *   
 *   Switch                   | Effect
 *   ------------------------ | --------------------------------------
 *   --ts PATH/TO/LTS.csv     | Determine the input transition system (must be given as a CSV with format:
 *   													|  "srcId, tarId, actionName". The internal action is denoted by "i".)
 *   --overapproximation ARG  | Which over-approximation to apply to keep the game small. (Default: bigstep, alternative: none)
 *   --preminimization ARG    | Which under-approximation to use for minimization at the beginning of the algorithm.
 *   													 (Default: delaybisim, alternative: weakbisim)
 *   --outputgame             | Whether to write the game to disk. (Will be written to input source path with ".game" appended)
 *   --checksoundness         | Check that the result relation really is a coupled simulation
 *   --parallelism N          | Degree of parallelism for the Flink program
 *   --sizemark               | Output sizes of systems, games, results for predefined benchmark set (takes a lot of time and space)
 *   --timemark               | Output running times for predefined benchmark set (takes a lot of time)   
 * 
 */
object CoupledSimulationFlink {
  
  final class Result(
      val relation: Option[Relation[Int]] = None,
      val sound: Option[Boolean] = None,
      val partitionRelation: (Map[Int, Int], Set[(Int, Int)]) = (Map(), Set()),
      val benchmarkSizes: Map[String, Long] = Map())
  
  val TAU_STR = "i"
  
  val MAX_ITERATIONS = 90000
  
  type Action = Long
  
  def graphToWeakTransitionSystem(tsGraph: Graph[Int, NullValue, Action], tau: Action) = {
    val tsEdges: Seq[Edge[Int,Long]] = tsGraph.getEdges.collect()
    val tsVerts: Seq[Int] = tsGraph.getVertexIds.collect()
    
    val trans = new LabeledRelation(for {
      edge <- tsEdges.toSet[Edge[Int,Long]]
    } yield (edge.getSource, edge.getValue, edge.getTarget))
    
    val nodes = tsVerts.map((_, 0)).toMap
    
    new WeakTransitionSystem(trans, nodes, Set(tau))
  }
  
  def crunchGraph(tsGraph: Graph[Int, NullValue, Action], partitionMap: DataSet[(Int, Coloring.Color)], env: ExecutionEnvironment)
  : Graph[Int, NullValue, Action] = {
    
    val crunchedGraphEdges = ((((partitionMap joinWithHuge tsGraph.getEdgesAsTuple3())
          .where(0).equalTo(0) ((pl, step) => (pl._2, step._2, step._3)))
        joinWithTiny partitionMap).where(1).equalTo(0) ((step, pr) => new Edge(step._1, pr._2, step._3)))
      .distinct()
      
    Graph.fromDataSet(crunchedGraphEdges, env)
  }
  
  def blowUpGraph(tsGraph: Graph[Int, NullValue, Action],
      partitionMapLeft: DataSet[(Int, Int)],
      partitionMapRight: DataSet[(Int, Int)],
      env: ExecutionEnvironment)
  : Graph[Int, NullValue, Action] = {
    
    val fullTransitions = 
        tsGraph.getEdgesAsTuple3()
        .join(partitionMapLeft)
          .where(0).equalTo(1).apply((step, mc) => (mc._1, step._2, step._3))
        .join(partitionMapRight)
          .where(1).equalTo(1) ((step, mc) => new Edge(step._1, mc._1, step._3))
    
    Graph.fromDataSet(fullTransitions, env)
  }
      
  def buildWeakTransitionGraph(tsGraph: Graph[Int, NullValue, Action], tau: Action, env: ExecutionEnvironment,
      tauMaximalSteps: Boolean = false, delayWeakSteps: Boolean = false)
    : (Graph[Int, NullValue, Long], DataSet[(Int, Int)]) = {
    
    val tauSteps: DataSet[(Int, Int)] = tsGraph.getEdgesAsTuple3() filter new FilterFunction[((Int, Int, Action))] {
      def filter(edge: ((Int, Int, Action))) = edge match {
        case ((p0, p1, a)) => a == tau && p0 != p1
      }
    } map (st => (st._1, st._2))
    
    val transitiveSteps: DataSet[(Int, Int)] = new TransitiveClosure().compute(tauSteps)
    
    val reflSteps: DataSet[(Int, Int)] = tsGraph.getVertexIds() map (v => (v,v))
    val closedTauStepsPre: DataSet[(Int, Int)] = transitiveSteps union reflSteps
    
    val closedTauStepsPost: DataSet[(Int, Int)] = if (tauMaximalSteps) {
      val tauMaximalStates: DataSet[Int] = (tsGraph.getVertexIds() leftOuterJoin tauSteps)
        .where(s => s).equalTo(0).apply( ((s: Int, st: (Int, Int), collector: Collector[Int]) => if (st == null) collector.collect(s) ))
      
      (tauMaximalStates join closedTauStepsPre).where(s => s).equalTo(1) ((s, st) => st)
    } else {
      closedTauStepsPre
    }
    
    val weakTransitionsLeft: DataSet[(Int, Int, Action)] = (closedTauStepsPre join tsGraph.getEdgesAsTuple3())
      .where(1).equalTo(0) ((l, r) => (l._1, r._2, r._3))
    val weakTransitions: DataSet[(Int, Int, Action)] = 
      if (delayWeakSteps) {
        weakTransitionsLeft 
      } else {
        (weakTransitionsLeft join closedTauStepsPost)
          .where(1).equalTo(0) ((l, r) => (l._1, r._2, l._3))
      }
    
    val weakTransitionsTau = (closedTauStepsPost map (s12 => (s12._1, s12._2, tau))) union weakTransitions
    
    val weakTransitionGraph: Graph[Int, NullValue, Long] = Graph.fromTupleDataSet(weakTransitionsTau, env)
    
    (weakTransitionGraph, closedTauStepsPre)
  }
  
  def getBigStepEquivalenceSigs(tsGraph: Graph[Int, NullValue, Action], tau: Action, env: ExecutionEnvironment)
    : DataSet[(Int, Set[(Coloring.Color, Coloring.Color)])] = {
    
    val (weakTransitionGraph, _) = buildWeakTransitionGraph(tsGraph, tau, env, tauMaximalSteps = true)
    
    val (_, signatures) = new SignatureRefinement().compute(weakTransitionGraph)
    
    val ts = graphToWeakTransitionSystem(tsGraph, tau)
    
    signatures
  }
  
  def getWeakBisim(tsGraph: Graph[Int, NullValue, Action], tau: Action, env: ExecutionEnvironment, delayBisim: Boolean = false)
  : (DataSet[(Int, Int)], Graph[Int, NullValue, Long]) = {
        
    // first crunch system using strong bisim
    val (strongBisim, _) = new SignatureRefinement().compute(tsGraph)
    
    val crunchedGraph = crunchGraph(tsGraph, strongBisim, env)
    
    val (weakTransitionGraph, _) = buildWeakTransitionGraph(crunchedGraph, tau, env, delayWeakSteps = delayBisim)
    
    val (partitions, _) = new SignatureRefinement().compute(weakTransitionGraph)
    
    val fullPartitions = (strongBisim join partitions).where(1).equalTo(0) ((map1, map2) => (map1._1, map2._2))
    
    (fullPartitions, blowUpGraph(weakTransitionGraph, strongBisim, strongBisim, env))

  }
  
  def getSymmetricPart(rel: DataSet[(Int, Int)]): DataSet[(Int, Int)] = {
    (rel join rel).where(0,1).equalTo(1,0) ((l, r) => l)
  }
  
  def getCycleEquivalence(tsGraph: Graph[Int, NullValue, Action], tau: Action, env: ExecutionEnvironment): (DataSet[(Int, Int)], Graph[Int, NullValue, Long]) = {
    
    val (weakTransitionGraph, tauClosure): (Graph[Int, NullValue, Long], DataSet[(Int, Int)]) =
      buildWeakTransitionGraph(tsGraph, tau, env, delayWeakSteps = true)
    
    val weakTransitionEq = getSymmetricPart(tauClosure)
    val partitions = weakTransitionEq.groupBy(0).minBy(1)
    
    (partitions, weakTransitionGraph)
  }
  
  def executeAlgorithm(
      env: ExecutionEnvironment,
      cfgPath: String,
      cfgPreminimization: String = "delaybisim",
      cfgOverApproximation: String = "bigstep",
      cfgOutputGame: Boolean = false,
      cfgOutputRelation: Boolean = false,
      cfgCheckSoundness: Boolean = false,
      cfgReturnRelation: Boolean = false,
      cfgBenchmarkSizes: Boolean = false,
      cfgReturnPartitionRelation: Boolean = false) = {
    
    /* Phase 1: Import the transition system */
    
    val ts0: Graph[Int, NullValue, String] = 
      Graph.fromCsvReader(env = env, pathEdges = cfgPath, quoteCharacterEdges = '"')
   
    val TAU: Action = 0
    
    // relabel the input to use Longs as IDs for the actions instead of Strings
    val (ts1: Graph[Int, NullValue, Action],
        actionIds: DataSet[(Action, String)]) = 
      new ActionsStringToLongRelabeling(ts0).compute(env, TAU_STR, TAU)
      
    /* Phase 2: Apply a minimization to the TS based on a finer notion of equivalence */
      
    val (preminimizationColorsA: DataSet[(Int, Int)], weakTransitionGraph: Graph[Int, NullValue, Long]) =
      if (cfgPreminimization == "weakbisim" || cfgPreminimization == "delaybisim") {
        getWeakBisim(ts1, TAU, env, delayBisim = (cfgPreminimization == "delaybisim"))
      } else {
        getCycleEquivalence(ts1, TAU, env)
      }
    
    // this senseless conversion is necessary because otherwise some internal bug of
    // the flink optimizer occurs where it tries to set InterestingProperties on the
    // bulk iteration node of preminimizationColorsA twice.
    val preminimizationColors: DataSet[(Int, Int)] = env.fromCollection(preminimizationColorsA.collect())
        
    val ts: Graph[Int, NullValue, Action] =
      crunchGraph(ts1, preminimizationColors, env)
      
    /* Phase 3: Use a coarser notion of equivalence for an over-approximation of the CS relation */
    
    val signatures: DataSet[(Int, Set[(Coloring.Color, Coloring.Color)])] =
      if (cfgOverApproximation == "bigstep")
        getBigStepEquivalenceSigs(ts, TAU, env)
      else
        env.fromCollection(Set[(Int, Set[(Coloring.Color, Coloring.Color)])]())
    
    /* Phase 4: Build the CS game graph */
    
    val (gameNodes, gameMoves) = new CoupledSimulationGameDiscovery().compute(
        ts,
        if (cfgOverApproximation != "none") Some(signatures) else None,
        TAU,
        env)
    
    if (cfgOutputGame) {
      val gameSink = gameMoves.writeAsCsv(
        filePath = cfgPath + ".game",
        rowDelimiter = "\n",
        fieldDelimiter = ",",
        writeMode = FileSystem.WriteMode.OVERWRITE)
    }
    
    val gameGraph: Graph[(Action, Int, Int), Int, NullValue] = Graph.fromTuple2DataSet[(Action, Int, Int), Int](
        edges = gameMoves,
        vertexValueInitializer = new MapFunction[(Action, Int, Int), Int] {
          def map(in: (Action, Int, Int)): Int = 0
        },
        env = env
    )
    
    
    /* Phase 5: Decide the game */
    
    val gameDecider = new SimpleGameDecider
    val decidedGame = gameDecider.compute(gameGraph, env)
    
    val defenderWinningAttackerNodes: DataSet[((Action, Int, Int), Int)] =
      decidedGame.getVerticesAsTuple2() filter ( v =>
        v._1._1 == CoupledSimulationGame.ATTACK && v._2 != SimpleGameDecider.ATTACKER_WIN_MAGIC_NUMBER)
    
    
    /* Phase 6: Output results*/
    
    val benchmarkSizes = if (cfgBenchmarkSizes) {
      Map(
          "systemStates" -> ts0.getVertices.count(),
          "systemTransitions" -> ts0.getEdges.count(),
          "systemWeakTransitions" -> weakTransitionGraph.getEdges.count(),
          "minimizedStates" -> ts.getVertices.count(),
          "minimizedTransitions" -> ts.getEdges.count(),
          "gameNodes" -> gameGraph.getVertices.count(),
          "gameMoves" -> gameGraph.getEdges.count()
      )
    } else {
      Map[String, Long]()
    }

    if (cfgReturnPartitionRelation) {
      val resultCoupledSimulation: DataSet[(Int, Int)] =
        defenderWinningAttackerNodes
        .distinct()
        .map ({ case (((_, p, q), _)) => (p, q) }: (((Action, Int, Int), Int)) => (Int, Int))
      
      // merge strongly connected components
      val csEq = getSymmetricPart(resultCoupledSimulation)
      // maps every node to a representative for its component
      val csPartitions = csEq.groupBy(0).min(1)
      
      val csPartitionsScala = csPartitions.collect().toMap
      val csRepresentativesScala = csPartitionsScala.values.toSet
      
      val csRelOnPartsScala = resultCoupledSimulation.collect().filter { case (p,q) =>
        csRepresentativesScala(p) && csRepresentativesScala(q)
      } toSet
      
      new Result(partitionRelation = (csPartitionsScala, csRelOnPartsScala), benchmarkSizes = benchmarkSizes)
      
    } else if (cfgOutputRelation || cfgReturnRelation || cfgCheckSoundness) {
    
      val resultCoupledSimulation: DataSet[(Int, Int)] =
        defenderWinningAttackerNodes
        .distinct()
        .map ({ case (((_, p, q), _)) => (p, q) }: (((Action, Int, Int), Int)) => (Int, Int))
        .join(preminimizationColors)
          .where(0).equalTo(1).apply((pq, mc) => (mc._1, pq._2))
        .join(preminimizationColors)
          .where(1).equalTo(1) ((pq, mc) => (pq._1, mc._1))
    
      if (cfgOutputRelation) {
        val sinkCoupledSimulation =
        resultCoupledSimulation.writeAsCsv(
            filePath = cfgPath + ".cs",
            rowDelimiter = "\n",
            fieldDelimiter = ",",
            writeMode = FileSystem.WriteMode.OVERWRITE).setParallelism(1)
      }
      
      if (cfgCheckSoundness || cfgReturnRelation) { 
        
        val fullBlownRelation = new Relation(resultCoupledSimulation.collect().toSet)
        
        if (cfgCheckSoundness) {
          println("[INFO] checking soundness (this may take a while)")
          
          val simulationChallenges: DataSet[(Action, Int, Int)] = (resultCoupledSimulation join ts1.getEdgesAsTuple3())
            .where(0).equalTo(0) ((pq, step) => (step._3, step._2, pq._2))
          val simulationAnswers: DataSet[(Action, Int, Int, Int)] = (((simulationChallenges join weakTransitionGraph.getEdgesAsTuple3())
              .where(0,2).equalTo(2,0) ((apq, step) => (apq._1, apq._2, apq._3, step._2)))
            join resultCoupledSimulation)
              .where(1,3).equalTo(0,1) ((answer, pair) => answer)
          val simulationCounterExamples: DataSet[(Action, Int, Int)] = (simulationChallenges leftOuterJoin simulationAnswers)
            .where(0,1,2).equalTo(0,1,2) ((challenge, answer, collector: Collector[(Action, Int, Int)]) =>
              if (answer == null) collector.collect(challenge))
          
          val couplingAnswers: DataSet[(Int, Int, Int)] =
            (((resultCoupledSimulation join weakTransitionGraph.getEdgesAsTuple3().filter(_._3 == TAU))
              .where(1).equalTo(0) ((pq, step) => (pq._1, pq._2, step._2)))
            join resultCoupledSimulation).where(2,0).equalTo(0,1) ((answer, pair) => answer) // note the inversion for coupling!
          val couplingCounterExamples: DataSet[(Int, Int)] = (resultCoupledSimulation leftOuterJoin couplingAnswers)
            .where(0,1).equalTo(0,1) ((challenge, answer, collector: Collector[(Int, Int)]) =>
              if (answer == null) collector.collect(challenge))
          
          if (simulationCounterExamples.count() == 0 && couplingCounterExamples.count() == 0) {
            println("[INFO] " + Console.GREEN + "Result relation is a coupled simulation.")
            new Result(relation = Some(fullBlownRelation), sound = Some(true))
          } else {
            println("[ERROR] " + Console.RED + "Result relatsion is NO coupled simulation. (This should actually not happen.)\n" +
                "Counter examples [first 5+5]:\n  Sim: " + simulationCounterExamples.first(5).collect() + "\n  Coupling: " + 
                 couplingCounterExamples.first(5).collect())
            new Result(relation = Some(fullBlownRelation), sound = Some(false), benchmarkSizes = benchmarkSizes)
          }
        } else {
          new Result(relation = Some(fullBlownRelation), benchmarkSizes = benchmarkSizes)
        }
      } else {
        env.execute()
        new Result(benchmarkSizes = benchmarkSizes)
      }  
    } else {
       val count = defenderWinningAttackerNodes.count()
       new Result(benchmarkSizes = benchmarkSizes)
    }
  }
  
  def main(args: Array[String]) {
    
    val params: ParameterTool = ParameterTool.fromArgs(args)

    val env = ExecutionEnvironment.getExecutionEnvironment
    
    env.getConfig.setGlobalJobParameters(params)

    //--ts /home/ben/Documents/coupledsim/code/shared/src/test/assets/csv/coupled-sim-1b.csv
    val cfgPath = params.get("ts", "shared/src/test/assets/csv/coupled-sim-1b.csv")
   
    val cfgOverApproximation = params.get("overapproximation", "bigstep")
    
    val cfgPreminimization = params.get("preminimization", "delaybisim")
      
    val cfgOutputGame = params.has("outputgame")
    
    val cfgCheckSoundness = params.has("checksoundness")
    
    if (params.has("parallelism")) {
      val parallelism = params.getInt("parallelism", 2)
      env.setParallelism(parallelism)
    }
    
    if (params.has("sizemark")) {
      CoupledSimulationFlinkBenchmark.runSizeMark(cfgPreminimization = cfgPreminimization, cfgOverApproximation = cfgOverApproximation)
    } else if (params.has("timemark")) {
      CoupledSimulationFlinkBenchmark.runTimeMark(cfgPreminimization = cfgPreminimization, cfgOverApproximation = cfgOverApproximation)
    } else {
      executeAlgorithm(env,
          cfgPath = cfgPath,
          cfgPreminimization = cfgPreminimization,
          cfgOverApproximation = cfgOverApproximation,
          cfgOutputGame = cfgOutputGame,
          cfgCheckSoundness = cfgCheckSoundness)
    }
    
  }
}
