package de.bbisping.coupledsim.algo

import utest._
import de.bbisping.coupledsim.algo.rt2010.SchematicSimilarity
import de.bbisping.coupledsim.tool.control.StructureOperation

/**
 * Tests that all simulation algorithms compute the same maximal simulations
 * like SchematicSimilarity for the whole TestSample set.
 */

object Simulations extends TestSuite{
  
  AlgorithmLogging.loggingActive = false
  
  val cannonicalSimulations = for {
    (slug, system) <- TestSamples.samples
    val rel = new SchematicSimilarity(system).compute()
  } yield (slug, system, rel)
  
  val simulationAlgos = List[StructureOperation.StructureRelationAnalyzer](
      new StructureOperation.RefinedSimilarityAnalyzer,
      new StructureOperation.BasicSASimilarityAnalyzer,
      new StructureOperation.RefinedSASimilarityAnalyzer,
      new StructureOperation.SASimilarityAnalyzer
  )
  
  def testSimulationAlgo()(implicit path: utest.framework.TestPath) = {
    val algoSlug = path.value.last
    for {
      algo <- simulationAlgos find (_.slug == algoSlug)
      (slug, system, cannonicalRel) <- cannonicalSimulations
    } {
      val (rel, _) = algo.analyze(system)
      println(slug)
      assert(rel == cannonicalRel)
    }
  }
  
  val tests = Tests{
    "refined-similarity" - testSimulationAlgo()
    //"hhk-similarity" - testSimulationAlgo() // broken :/
    "basic-sa-similarity" - testSimulationAlgo()
    "refined-sa-similarity" - testSimulationAlgo()
    //"sa-similarity" - testSimulationAlgo() // does not yet work
  }
}