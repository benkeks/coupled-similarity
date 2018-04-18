package de.bbisping.coupledsim.algo

import de.bbisping.coupledsim.ts.TransitionSystem
import de.bbisping.coupledsim.util.FixedPoint
import de.bbisping.coupledsim.util.Coloring

/**
 * Implementation of Naive Iterative Refinement from [BGR 2016]
 * 
 * */

class NaiveStrongBisimC[S, A, L] (
    override val ts: TransitionSystem[S, A, L])
  extends IterativeRefinementC[S, A, L] {
  
  val labelColors = {
    val parts = for {
      (_, s) <- ts.nodesByLabel
    } yield s
    Coloring.fromPartition(parts.toSet)
  }
  
  val actionColors =
    Coloring.fromPartition(ts.actions.map(Set(_)).toSet)
  
  override def initialApproximation: Coloring[S] = {
    // first step approximation for node-labeled transition systems
    labelColors
  }
  
  override def computeAfters(part: Coloring[S]): Map[S, Set[(Coloring.Color, Coloring.Color)]] = {
    val aft = for {
      (n, a, m) <- ts.step.tupleSet
      //TODO: see whether labelColors should also be included
    } yield (n, (actionColors(a), part(m)))
    aft.groupBy(_._1).mapValues(_.map(_._2))
    
    // [DPP2004, Section 7] proves (?) that the node labeling should only matter in the initializing phase.
    // --> so why do I seem to need it here?!
  }
  
  override def refine(part: Coloring[S], coloredAfters: Map[S, Set[(Coloring.Color, Coloring.Color)]])(implicit cmp: Ordering[S]): Coloring[S] = {
    (part.splitInsertColors(coloredAfters)).normalize
  }
}