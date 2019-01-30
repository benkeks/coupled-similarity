package de.bbisping.coupledsim.flink

import org.apache.flink.api.scala.ExecutionEnvironment

import scala.collection.Seq

/**
  * Runs the coupled simulation flink algorithm on a number of VLTS samples
  * in order to produce the benchmarking results as reported in our TACAS 2019
  * paper.
  */
object TacasBenchmarks {
  
  val tacasSamples = Seq(
    "shared/src/test/assets/csv/coupled-sim-phil.csv",
    "shared/src/test/assets/csv/ltbts.csv",
    "shared/src/test/assets/vlts/vasy_0_1.csv", //   289,   1224,  no tau,  2
    "shared/src/test/assets/vlts/vasy_1_4.csv", //  1183,   4464,    1213,  6
    "shared/src/test/assets/vlts/vasy_5_9.csv",
    "shared/src/test/assets/vlts/cwi_1_2.csv", //  1952,   2387,    2215, 26
    "shared/src/test/assets/vlts/cwi_3_14.csv",//  3996,  14552,   14551,  2
    "shared/src/test/assets/vlts/vasy_8_24.csv",
    "shared/src/test/assets/vlts/vasy_8_38.csv",
    "shared/src/test/assets/vlts/vasy_10_56.csv",
    "shared/src/test/assets/vlts/vasy_25_25.csv"
  )

  val systemPathToTacasHandle = Map(
    "shared/src/test/assets/csv/coupled-sim-phil.csv" -> "phil",
    "shared/src/test/assets/csv/ltbts.csv" -> "ltbts"
  ).withDefault(s => s.slice(s.lastIndexOf('/') + 1, s.lastIndexOf('.')))

  def runSizeMark(cfgPreminimization: String, cfgOverApproximation: String): Unit = {
    val samples = tacasSamples
    
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
  def runTacasMark(): Unit = {
    val samples = tacasSamples

    val cfgOverApproximation = "bigstep"
    val cfgPreminimization = "delaybisim"

    val env = ExecutionEnvironment.getExecutionEnvironment
    env.getConfig.disableSysoutLogging()
    env.setParallelism(4)

    println("Warmup for time benchmark using the first four systems...")

    for (s <- samples.take(4)) {

      val begin = System.currentTimeMillis()

      CoupledSimulationFlink.executeAlgorithm(env,
        cfgPath = s,
        cfgPreminimization = cfgPreminimization,
        cfgOverApproximation = cfgOverApproximation)

      val time = System.currentTimeMillis() - begin
    }

    println("\nTime Benchmark\n")

    println("system, time/s")

    for (s <- samples) {
      
      val begin = System.currentTimeMillis()
      
      CoupledSimulationFlink.executeAlgorithm(env,
          cfgPath = s,
          cfgPreminimization = cfgPreminimization,
          cfgOverApproximation = cfgOverApproximation)
          
      val time = System.currentTimeMillis() - begin

      println(systemPathToTacasHandle(s) + ", " + time)
    }

    println("\nSystem sizes\n")

    println("S, ->, =|>, S_DBquotient, >->")

    for (s <- samples.dropRight(2)) {

      val begin = System.currentTimeMillis()

      val csResult = CoupledSimulationFlink.executeAlgorithm(env,
        cfgPath = s,
        cfgPreminimization = cfgPreminimization,
        cfgOverApproximation = "none",
        cfgBenchmarkSizes = true,
        cfgReturnPartitionRelation = true)

      val time = System.currentTimeMillis() - begin
      val benchmark = csResult.benchmarkSizes.withDefaultValue("")

      println(systemPathToTacasHandle(s) + ", " +
        benchmark("systemStates") + ", " +
        benchmark("systemTransitions") + ", " +
        benchmark("systemWeakTransitions") + ", " +
        benchmark("minimizedStates") + ", " +
        benchmark("gameMoves"))
    }
    //vasy_10_56 and vasy_25_25 are omitted as they would crash due to the unoptimized game not
    //fitting into the memory.]")
    println("vasy_10_56, o.o.m")
    println("vasy_25_25, o.o.m")

    println("\n>->_sigma, S_CSquotient, CSonQuotient")

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

      println(systemPathToTacasHandle(s) + ", " +
        benchmark("gameMoves") + ", " +
        csPartitionCount + ", " +
        csRel.size)
    }

  }


}