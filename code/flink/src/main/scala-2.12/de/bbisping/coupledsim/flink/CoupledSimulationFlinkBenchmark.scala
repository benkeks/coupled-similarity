package de.bbisping.coupledsim.flink

import org.apache.flink.api.scala.ExecutionEnvironment
import scala.collection.Seq


/**
 * Runs the coupled simulation flink algorithm on a number of VLTS samples
 */
object CoupledSimulationFlinkBenchmark {
  
  val smallSamples = Seq(
    "shared/src/test/assets/csv/alphabet.csv",
    "shared/src/test/assets/csv/bug1.csv",
    "shared/src/test/assets/csv/bug2.csv",
    "shared/src/test/assets/csv/contra-sim-1.csv",
    "shared/src/test/assets/csv/coupled-sim-1b.csv",
    "shared/src/test/assets/csv/coupled-sim-2.csv",
    "shared/src/test/assets/csv/coupled-sim-phil.csv",
    "shared/src/test/assets/csv/diamond.csv",
    "shared/src/test/assets/csv/ltbts.csv",
    "shared/src/test/assets/csv/sim-1.csv",
    "shared/src/test/assets/csv/weak-bisim-1.csv",
    "shared/src/test/assets/csv/weak-bisim-2.csv",
    "shared/src/test/assets/csv/weak-bisim-2b.csv"
  )
  
  val vltsSamplesSmall = Seq(
    "shared/src/test/assets/vlts/vasy_0_1.csv" //   289,   1224,  no tau,  2
  )
    
  val vltsSamplesMedium = Seq(
    "shared/src/test/assets/vlts/vasy_1_4.csv", //  1183,   4464,    1213,  6
    "shared/src/test/assets/vlts/vasy_5_9.csv",
    "shared/src/test/assets/vlts/cwi_1_2.csv", //  1952,   2387,    2215, 26
    "shared/src/test/assets/vlts/cwi_3_14.csv",//  3996,  14552,   14551,  2
    "shared/src/test/assets/vlts/vasy_8_24.csv",
    "shared/src/test/assets/vlts/vasy_8_38.csv",
    "shared/src/test/assets/vlts/vasy_10_56.csv",
//    "shared/src/test/assets/vlts/vasy_18_73.csv" // memory ran out (in discovery)
    "shared/src/test/assets/vlts/vasy_25_25.csv"
  //  "shared/src/test/assets/vlts/vasy_40_60.csv"
      /*
        transitive closure on vasy_40_60 takes forever (also 15 secs in the optimized [BGR2016] implementation);
        weak bisim result probably wrong due to hash collisions
      */
  )
  
  def runSizeMark(cfgPreminimization: String, cfgOverApproximation: String): Unit = {
    val samples = // List("shared/src/test/assets/vlts/vasy_40_60.csv")
      smallSamples ++
      vltsSamplesSmall ++
      vltsSamplesMedium
    
    val env = ExecutionEnvironment.getExecutionEnvironment
    env.getConfig.disableSysoutLogging()
    
    for (s <- samples) {
      
      val begin = System.currentTimeMillis()
      
      val csResult = CoupledSimulationFlink.executeAlgorithm(env,
          cfgPath = s,
          cfgPreminimization = cfgPreminimization,
          cfgOverApproximation = cfgOverApproximation,
          cfgBenchmarkSizes = true,
          cfgReturnPartitionRelation = true)
          
      val time = System.currentTimeMillis() - begin
      val benchmark = csResult.benchmarkSizes.withDefaultValue("")
      val (csPart, csRel) = csResult.partitionRelation
      val csPartitionCount = csPart.values.toSet.size
      
      println(s + ", " + 
          benchmark("systemStates") + ", " +
          benchmark("systemTransitions") + ", " +
          benchmark("systemWeakTransitions") + ", " +
          benchmark("minimizedStates") + ", " +
          benchmark("minimizedTransitions") + ", " +
          benchmark("gameNodes") + ", " +
          benchmark("gameMoves") + ", " +
          csPartitionCount + ", " +
          csRel.size + ", " +
          time)
    }
  }
  
  def runTimeMark(cfgPreminimization: String, cfgOverApproximation: String): Unit = {
    val samples = 
      smallSamples ++ // warmup
      smallSamples ++ 
      vltsSamplesSmall ++
      vltsSamplesMedium
    
    val env = ExecutionEnvironment.getExecutionEnvironment
    env.getConfig.disableSysoutLogging()
    
    for (s <- samples) {
      
      val begin = System.currentTimeMillis()
      
      CoupledSimulationFlink.executeAlgorithm(env,
          cfgPath = s,
          cfgPreminimization = cfgPreminimization,
          cfgOverApproximation = cfgOverApproximation)
          
      val time = System.currentTimeMillis() - begin
      
      println(s + ", " + time)
    }
  }
  
}