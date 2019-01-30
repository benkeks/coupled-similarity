package de.bbisping.coupledsim.tool.control

import scala.scalajs.js.Date

import de.bbisping.coupledsim.algo.transform.AGraphConstruction
import de.bbisping.coupledsim.algo.AlgorithmLogging
import de.bbisping.coupledsim.algo.NaiveDivergenceFinder
import de.bbisping.coupledsim.algo.NaiveReflexiveClosure
import de.bbisping.coupledsim.algo.NaiveStrongBisimC
import de.bbisping.coupledsim.algo.NaiveTransitiveClosure
import de.bbisping.coupledsim.algo.RemoveEndoTransitions
import de.bbisping.coupledsim.algo.WeakStepAdder
import de.bbisping.coupledsim.algo.cs.BasicSACoupled
import de.bbisping.coupledsim.algo.cs.FixedPointCoupledSimilarity
import de.bbisping.coupledsim.algo.cs.GameCoupledSimilarity
import de.bbisping.coupledsim.algo.cs.SchematicCoupledSimilarity
import de.bbisping.coupledsim.algo.cs.GameCoupledSimilarityPlain
import de.bbisping.coupledsim.algo.rt2010.BasicSA
import de.bbisping.coupledsim.algo.rt2010.BasicSAWeak
import de.bbisping.coupledsim.algo.rt2010.RefinedSA
import de.bbisping.coupledsim.algo.rt2010.RefinedSimilarity
import de.bbisping.coupledsim.algo.rt2010.SA
import de.bbisping.coupledsim.algo.rt2010.SchematicSimilarity
import de.bbisping.coupledsim.algo.sigref
import de.bbisping.coupledsim.checkers.NaiveCoupledSimCheck
import de.bbisping.coupledsim.tool.control.Structure.ActionLabel
import de.bbisping.coupledsim.tool.model.NodeID
import de.bbisping.coupledsim.ts.DivergenceInformation
import de.bbisping.coupledsim.ts.TransitionSystem
import de.bbisping.coupledsim.ts.WeakTransitionSystem
import de.bbisping.coupledsim.util.Coloring
import de.bbisping.coupledsim.util.LabeledRelation
import de.bbisping.coupledsim.util.Relation
import de.bbisping.coupledsim.algo.RemoveInstableStates
import de.bbisping.coupledsim.algo.transform.TauLoopCompression
import de.bbisping.coupledsim.algo.transform.BuildQuotientSystem
import de.bbisping.coupledsim.algo.transform.PS94CSNormalForms

trait StructureOperation {
  
  val name: String
  
  val slug: String
  
  val category: String = "default"
  
  val description: String = ""
  
  def applyOperation(system: Structure): Unit
  
  override def toString() = slug
}

object StructureOperation {
    
  /** Some analyzer which returns a coloring/partition of nodes. */
  trait StructureAnalyzer extends StructureOperation {
    
    def analyze(system: Structure.TSStructure): Coloring[NodeID]
    
    /** calls the analyzer and sets the current partition for the structure. */
    override def applyOperation(structure: Structure): Unit = {
      val begin = Date.now
      val c = analyze(structure.structure)
      println("Analyzer «" + name + "» took: " + (Date.now - begin) + "ms.")
      structure.setPartition(c)
    }
  }
  
  class NaiveStrongBisimAnalyzer extends StructureAnalyzer {
    
    override val name = "Naive Strong Bisim"
    
    override val slug = "naive-strong-bisim"
    
    override val category = "SimBisim"
    
    override val description =
      "Computes the strong bisimilarity coloring, " +
      "using the naive interative approach [BGR16]."
    
    override def analyze(system: Structure.TSStructure) = new NaiveStrongBisimC(system).compute()
    
  }
  
  class NaiveDivergenceAnalyzer extends StructureAnalyzer {
    
    override val name = "Naive Divergence Finder"
    
    override val slug = "naive-divergence-finder"
    
    override def analyze(system: Structure.TSStructure) = new NaiveDivergenceFinder(system).compute()
    
  }
  
  /** Some analyzer which returns a relation on nodes. */
  trait StructureRelationAnalyzer extends StructureOperation {
    
    def analyze(system: Structure.TSStructure): (Relation[NodeID], Option[AlgorithmLogging[NodeID, Structure.ActionLabel, Structure.NodeLabel]])
    
    /** calls the analyzer and sets the current relation for the structure. */
    override def applyOperation(structure: Structure): Unit = {
      val begin = Date.now
      val (r, log) = analyze(structure.structure)
      println("Analyzer «" + name + "» took: " + (Date.now - begin) + "ms.")
      structure.setRelation(r)
      for {l <- log} structure.setReplay(l.getReplay())
    }
  }
  
  class SchematicSimilarityAnalyzer extends StructureRelationAnalyzer {
    
    override val name = "Schematic Similarity"
    
    override val slug = "schematic-similarity"
    
    override val category = "SimBisim"
    
    override val description =
      "Computes the strong simulation preorder relation in the simplest conceivable way [RT10]."
      
    override def analyze(system: Structure.TSStructure) = {
      val algo = new SchematicSimilarity(system)
      (algo.compute(), Some(algo))
    }
    
  }
  
  class RefinedSimilarityAnalyzer extends StructureRelationAnalyzer {
    
    override val name = "Refined Similarity"
    
    override val slug = "refined-similarity"
    
    override val category = "SimBisim"
    
    override val description =
      "Computes the strong simulation preorder relation " +
      "by a refined similarity algorithm [RT10]."
    
    override def analyze(system: Structure.TSStructure) = (new RefinedSimilarity(system).compute(), None)
    
  }
  
  class BasicSASimilarityAnalyzer extends StructureRelationAnalyzer {
    
    override val name = "BasicSA Similarity"
    
    override val slug = "basic-sa-similarity"
    
    override val category = "SimBisim"
    
    override val description =
      "Computes the strong simulation preorder relation " +
      "by the BasicSA algorithm from [RT10]."
    
    override def analyze(system: Structure.TSStructure) = {
      val algo = new BasicSA(system)
      (algo.compute(), Some(algo))
    }
  }
  
  class BasicSAWeakSimilarityAnalyzer extends StructureRelationAnalyzer {
    
    override val name = "BasicSA Similarity Weak"
    
    override val slug = "basic-sa-similarity-weak"
    
    override val category = "SimBisim"
    
    override val description =
      "Computes the weak simulation preorder relation " +
      "by a modified version of the BasicSA algorithm from [RT10]."
    
    override def analyze(system: Structure.TSStructure) = {
      val algo = new BasicSAWeak(system)
      (algo.compute(), Some(algo))
    }
  }
  
  class RefinedSASimilarityAnalyzer extends StructureRelationAnalyzer {
    
    override val name = "RefinedSA Similarity"
    
    override val slug = "refined-sa-similarity"
    
    override val category = "SimBisim"
    
    override def analyze(system: Structure.TSStructure) = {
      val algo = new RefinedSA(system)
      (algo.compute(), Some(algo))
    }
  }
  
  /* not completed! */
  class SASimilarityAnalyzer extends StructureRelationAnalyzer {
    
    override val name = "SA Similarity (incomplete!)"
    
    override val slug = "sa-similarity"
    
    override val category = "SimBisim"
    
    override def analyze(system: Structure.TSStructure) = {
      val algo = new SA(system)
      (algo.compute(), Some(algo))
    }
  }
  
  class SigrefBisimilarityAnalyzer extends StructureRelationAnalyzer {
    
    override val name = "Sigref Bisimilarity"
    
    override val slug = "sigref-bisimilarity"
    
    override val category = "SimBisim"

    override val description =
      "Computes the strong bisimilarity relation " +
      "by iterating a signature refinement algorithm [Wim11]."
    
    override def analyze(system: Structure.TSStructure) = {
      val algo = new sigref.Bisimilarity(system)
      (algo.compute(), Some(algo))
    }
  }
  
  class SigrefWeakBisimilarityAnalyzer extends StructureRelationAnalyzer {
    
    override val name = "Sigref Weak Bisimilarity"
    
    override val slug = "sigref-weak-bisimilarity"
    
    override val category = "SimBisim"
    
    override val description =
      "Computes the weak bisimilarity relation " +
      "by iterating a signature refinement algorithm [Wim11]."
    
    override def analyze(system: Structure.TSStructure) = {
      val algo = new sigref.WeakBisimilarity(system)
      (algo.compute(), Some(algo))
    }
  }
  
  class SchematicCoupledSimilarityAnalyzer extends StructureRelationAnalyzer {
    
    override val name = "Schematic Coupled Similarity"
    
    override val slug = "schematic-coupled-similarity"
    
    override def analyze(system: Structure.TSStructure) = (new SchematicCoupledSimilarity(system).compute(), None)
  }
  
  class FixedPointCoupledSimilarityAnalyzer extends StructureRelationAnalyzer {
    
    override val name = "Fixed-Point Coupled Similarity"
    
    override val slug = "fixed-point-coupled-similarity"
    
    override val description =
      "Computes the coupled simulation preorder (relation) " +
      "by iterating to the greatest fixed point of the coupled simulation rules. (Sec 4.3 in the thesis)"
    
    override def analyze(system: Structure.TSStructure) = (new FixedPointCoupledSimilarity(system).compute(), None)
  }
  
  
  /* does not yet work */
  class BasicSACoupledSimilarityAnalyzer extends StructureRelationAnalyzer {
    
    override val name = "BasicSA Coupled Similarity (unfinished)"
    
    override val slug = "basic-sa-coupled-similarity"
    
    override def analyze(system: Structure.TSStructure) = {
      val algo = new BasicSACoupled(system)
      (algo.compute(), Some(algo))
    }
  }
  
  class GameCoupledSimilarityAnalyzer extends StructureRelationAnalyzer {
    
    override val name = "Game Coupled Similarity"
    
    override val slug = "game-coupled-similarity"
    
    override val description =
      "Computes the coupled simulation preorder (relation) " +
      "by solving the minimized coupled simulation game. (Sec 4.5 in the thesis)"
    
    override def analyze(system: Structure.TSStructure) = {
      val algo = new GameCoupledSimilarity(system)
      (algo.compute(), Some(algo))
    }
  }
  
  class GameCoupledSimilarityPlainAnalyzer extends StructureRelationAnalyzer {
    
    override val name = "Game Coupled Similarity Plain"
    
    override val slug = "game-coupled-similarity-plain"
    
    override val description =
      "Computes the coupled simulation preorder (relation) " +
      "by solving the full-blown coupled simulation game. (Sec 4.4 in the thesis)"
      
    override def analyze(system: Structure.TSStructure) = {
      val algo = new GameCoupledSimilarityPlain(system)
      (algo.compute(), Some(algo))
    }
  }
  
  class TauClosureCoupledSimilarityAnalyzer extends StructureAnalyzer {
    
    override val name = "Bisimulation Reduction Coupled Similarity"
    
    override val slug = "tau-closure-coupled-similarity"
    
    override val description =
      "Computes a coupled similarity partitioning (coloring) of the nodes " +
      "by reducing the problem to strong bisimilarity using the [PS94]-CS-Normalizer Closure. (Sec 4.2 in the thesis)"
    
    override def analyze(system: Structure.TSStructure) = {
      val psCSTauClosureSystem = new PS94CSNormalizer().transform(system)
      val csWeakStepSystem = new NaiveReflexiveTauClosure().transform(psCSTauClosureSystem)
      
      new sigref.Bisimilarity(csWeakStepSystem).computePartition().filter(system.nodes)
    }
  }
  
  class NaiveCoupledSimChecker extends StructureOperation {
    
    override val name = "Coupled Simulation Checker"
    
    override val slug = "naive-coupled-simulation-checker"
    
    override val description =
      "Checks whether all tuples in a relation respect coupled simulation. (If there are counter examples, they will be marked in red.)"
      
    override def applyOperation(structure: Structure): Unit = {
      val begin = Date.now
      val r = new NaiveCoupledSimCheck(structure.structure, structure.relation.toRelation).check()
      println("Analyzer «" + name + "» took: " + (Date.now - begin) + "ms.")
      val relationAnnotation = for { ((p1, p2), l) <- r } yield (p1, l, p2)
      structure.setRelation(structure.relation merge new LabeledRelation(relationAnnotation))
    }
  }
  
  trait StructureTransformer extends StructureOperation {
    
    def transform(system: Structure.TSStructure): Structure.TSStructure
    
    override def applyOperation(structure: Structure) = {
      val begin = Date.now
      val c = transform(structure.structure)
      println("Transformer «" + name + "» took: " + (Date.now - begin) + "ms.")
      structure.setStructure(c)
    }
  }
  
  class NaiveDivergenceMarker extends StructureTransformer {
    
    override val name = "Naive Divergence Marker"
    
    override val slug = "naive-divergence-marker"
    
    override def transform(system: Structure.TSStructure): Structure.TSStructure = {
      val coloring = new NaiveDivergenceFinder(system).compute()
      
      new WeakTransitionSystem(system.step, system.nodeLabeling, system.silentActions) with DivergenceInformation[NodeID] {
        def diverges(s: NodeID): Boolean =
          coloring.colors(s) == 1
      }
    }
  }
  
  class NaiveTransitiveTauClosure extends StructureTransformer {
    
    override val name = "Transitive Tau Closure"
    
    override val slug = "naive-trans-tau-closure"
    
    override val category = "Closures"
    
    override val description =
      "Adds transitive closure of tau-steps."
    
    override def transform(system: Structure.TSStructure) = {
      val trans = new NaiveTransitiveClosure(system, system.silentActions).compute()
      Structure.transitionSystemConstructor(trans, system.nodeLabeling, Some(system))
    }
  }
  
  class NaiveReflexiveTauClosure extends StructureTransformer {
    
    override val name = "Reflexive Tau Closure"
    
    override val slug = "naive-refl-tau-closure"
    
    override val category = "Closures"
    
    override val description =
      "Adds reflexive closure of tau-steps."
    
    override def transform(system: Structure.TSStructure) = {
      val newTrans = new NaiveReflexiveClosure(system, Structure.silentActionLabel).compute()
      Structure.transitionSystemConstructor(newTrans.step, newTrans.nodeLabeling, Some(system))
    }
  }
  
  
  class WeakStepRelationClosure extends StructureTransformer {
    
    override val name = "Weak Step Relation Closure"
    
    override val slug = "weak-step-relation-closure"
    
    override val category = "Closures"
    
    override val description =
      "Adds visible steps after transitive tau-closure."
    
    override def transform(system: Structure.TSStructure) = {
      val trans = new WeakStepAdder(system, system.silentActions).compute()
      Structure.transitionSystemConstructor(trans, system.nodeLabeling, Some(system))
    }
  }
  
  class RemoveTauEndoSteps extends StructureTransformer {
    
    override val name = "Remove Tau Endo-Steps"
    
    override val slug = "remove-tau-endo-steps"
    
    override val category = "Closures"
    
    override def transform(system: Structure.TSStructure) = {
      val trans = new RemoveEndoTransitions(system, Set()).compute()
      Structure.transitionSystemConstructor(trans, system.nodeLabeling, Some(system))
    }
  }
  
  class InstableStateRemover extends StructureTransformer {
    
    override val name = "Remove Instable Non-Divergent States"
    
    override val slug = "remove-instable-states"
    
    override val category = "Closures"
    
    override def transform(system: Structure.TSStructure) = {
      val trans = new RemoveInstableStates(system).compute()
      Structure.transitionSystemConstructor(trans, system.nodeLabeling, Some(system))
    }
  }
  
  class NaiveObservableDeterminismAdder extends StructureTransformer {
    
    override val name = "Naive Observable Determinism Adder"
    
    override val slug = "naive-observable-determinism-adder"
    
    override val category = "Closures"
    
    override def transform(system: Structure.TSStructure) = {
      val newNodes = for {
        ids <- system.nodes
      } yield (ids, NodeID.freshNodeID(system, ids))
      val nodeFactory = { (n: NodeID, i: Int) => NodeID.freshNodeID(system, n, i) }
      val newTrans = system // new NaiveDeterminismAdder(system, nodeFactory, system.nodes).compute()
      Structure.transitionSystemConstructor(newTrans.step, newTrans.nodeLabeling, Some(system))
    }
  }
  
  class AGraphConstructor extends StructureTransformer {
    
    override val name = "AGraph Constructor"
    
    override val slug = "agraph-constructor"
    
    override val category = "Closures"
    
    override val description =
      "Constructs 'AGraphs' as described by [CH93]. On AGraphs, bisimilar states correspond to trace equivalent states " +
      "of the initial systems. The algorithm needs an 'initial' state---we just take the upmost state (with the minimal y value)."
    
    override def transform(system: Structure.TSStructure): Structure.TSStructure = {
      
      val divColoring = new NaiveDivergenceFinder(system).compute()
      
      val systemWithDivergence = new WeakTransitionSystem(system.step, system.nodeLabeling, system.silentActions) with DivergenceInformation[NodeID] {
        def diverges(s: NodeID): Boolean =
          divColoring.colors(s) == 1
      }
      
      def newState(ts: WeakTransitionSystem[NodeID, Structure.ActionLabel, Structure.NodeLabel], acc: Set[Structure.ActionLabel], c: Boolean): (NodeID, Structure.NodeLabel) = {
        val id = NodeID.freshNodeID(ts, NodeID(acc.mkString("_") + "__" + c))
        val label = Structure.NodeLabel(acc.map(_.act))
        (id, label)
      }
      
      val constr = new AGraphConstruction(systemWithDivergence, newState)
      
      val (newTrans, newInitial) = constr.compute(systemWithDivergence.nodes.minBy(n => system.nodeLabeling(n).y.getOrElse(Double.MaxValue)))
      
      Structure.transitionSystemConstructor(newTrans.step, newTrans.nodeLabeling, Some(system))
    }
  }
  
  class PS94CSNormalizer extends StructureTransformer {
    
    override val name = "PS94 CS Normalalizer"
    
    override val slug = "ps94-cs-normalalizer"
    
    override val category = "Closures"
    
    override val description =
      "Builds CS-normal forms in the spirit of [PS94] (Sec 4.2 in the thesis). (For a full reduction to bisimulation, you must afterwards perform a reflexive tau closure)"
    
    override def transform(system: Structure.TSStructure): Structure.TSStructure = {
      
      var stateId = 0
      def newState(s: NodeID) = {
        stateId += 1
        NodeID.freshNodeID(system, NodeID(s.name + "__partial__"), stateId)
      }
      
      new PS94CSNormalForms(system, newState).compute()
    }
  }
  
  
  class TauLoopCompressor extends StructureTransformer {
    
    override val name = "Tau-loop Compression"
    
    override val slug = "tau-loop-compression"
    
    override val category = "Compressions"
    
    override val description =
      "Compresses tau loops to tau cycles (Sec 4.1.1 of the thesis)."
    
    override def transform(system: Structure.TSStructure) = {
      new TauLoopCompression(system).compute()
    }
  }
  
  class QuotientBuilder extends StructureOperation {
    
    override val name = "Quotient Builder"
    
    override val slug = "quotient-builder"
    
    override val category = "Compressions"
    
    override val description =
      "Compresses a transition system to a quotient system based on the current coloring (Sec 4.1.2 of the thesis)."
    
    override def applyOperation(structure: Structure) = {
      val begin = Date.now
      val c = new BuildQuotientSystem(structure.structure, structure.partition).build()
      println("Transformer «" + name + "» took: " + (Date.now - begin) + "ms.")
      structure.setStructure(c)
    }
  }
  
}
