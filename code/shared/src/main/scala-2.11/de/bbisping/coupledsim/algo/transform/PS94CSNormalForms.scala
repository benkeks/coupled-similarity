package de.bbisping.coupledsim.algo.transform

import scala.annotation.migration
import de.bbisping.coupledsim.ts.TransitionSystem
import de.bbisping.coupledsim.util.LabeledRelation
import de.bbisping.coupledsim.ts.WeakTransitionSystem
import de.bbisping.coupledsim.util.FixedPoint

/**
 * Performs a weak step closure skipping non-maximal tau-steps, combined with a closure
 * of partial sums following [PS94].
 * 
 * does not respect node labeling.
 * assumes that tau cycles have been compressed.
 */
class PS94CSNormalForms[S, A, L] (
    ts: WeakTransitionSystem[S, A, L],
    newState: (S) => S 
    ) {
    
  private val newStates: collection.mutable.Map[(Set[(A,S)]), S] = collection.mutable.Map()
    
  def compute() = {
    FixedPoint[WeakTransitionSystem[S, A, L]](computeStep _, (ts1, ts2) => ts1.nodes.size == ts2.nodes.size) (ts)
  }
    
  def computeStep(ts1: WeakTransitionSystem[S, A, L]) = { 
    
    val tauMaximalNodes = for {
      p <- ts1.nodes
      if ts1.silentReachable(p) subsetOf Set(p)
    } yield p
    
    // clause 2 and 3 of Def 17 from [PS94]
    val weakSteps = for {
      s <- ts1.nodes
      s1 <- ts1.silentReachable(s)
      (a, s2s) <- ts1.post(s1).toSet
      s2 <- s2s
      s3 <- ts1.silentReachable(s2)
      if (!ts1.silentActions(a) || tauMaximalNodes(s3) || s == s3)
    } yield (s, a, s3)
    
    val weakStepRel = new LabeledRelation(weakSteps)
    
    // clause 4 of [PS94]
    val partialCommits = for {
      (s, a, s1) <- weakSteps
      if !(tauMaximalNodes(s1))
      val s1edges = weakStepRel.rep(s1).toSet[(A, Set[S])].flatMap {
        case (a2, ss) =>
          for {
            s2 <- ss
            if !(ts1.silentActions(a2)) || s2 != s1
          } yield (a2, s2)
      }
      partialSum <- s1edges.subsets()
      if partialSum.size < s1edges.size &&
        (partialSum exists { as => ts1.silentActions(as._1) })
      val partialSumState = newStates.getOrElseUpdate(partialSum, newState(s1))
    } yield (s, a, s1, partialSumState, ts1.nodeLabeling(s1), partialSum)
    
    val newNodeLabels = for {
      (_, _, _, newPartialSumState, label, _) <- partialCommits
    } yield (newPartialSumState, label)
    
    val newInEdges = for {
      (s, a, _, newPartialSumState, _, _) <- partialCommits
    } yield (s, a, newPartialSumState)
    
    val newOutEdges = for {
      (s, _, s1, newPartialSumState, _, partialSum) <- partialCommits
      (a2, s2) <- partialSum
    } yield (newPartialSumState, a2, s2)
    
    val weakStepRelPartialSumClosed = new LabeledRelation(weakSteps ++ newInEdges ++ newOutEdges)
    
    println("ps94 normalization with " + (newInEdges++newOutEdges).size + " partial sum edges and "
        + newNodeLabels.size + " partial sum nodes.")
    
    new WeakTransitionSystem(weakStepRelPartialSumClosed, ts1.nodeLabeling ++ newNodeLabels, ts1.silentActions)
    
  }
  
}