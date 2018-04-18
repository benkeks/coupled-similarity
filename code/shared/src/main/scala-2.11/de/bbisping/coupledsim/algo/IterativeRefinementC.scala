package de.bbisping.coupledsim.algo

import de.bbisping.coupledsim.ts.TransitionSystem
import de.bbisping.coupledsim.util.Coloring
import de.bbisping.coupledsim.util.FixedPoint

/**
 * Iterative Refinement Skeleton roughly following 
 * "Computing maximal weak and other bisimulations" [BGR 2016]
 */
trait IterativeRefinementC[S, A, L] {
  
  val ts: TransitionSystem[S, A, L]
  
  def initialApproximation: Coloring[S]
  
  def computeAfters(part: Coloring[S]): Map[S, Set[(Coloring.Color, Coloring.Color)]]
  
  def refine(part: Coloring[S], coloredAfters: Map[S, Set[(Coloring.Color, Coloring.Color)]])(implicit cmp: Ordering[S]): Coloring[S]
  
  def compute()(implicit cmp: Ordering[S]) = {

    FixedPoint[Coloring[S]] (
      (p => {
        //println("pa: " + p.toPartition())
        val cs = computeAfters(p)
        //println("cs: " + cs)
        refine(p, cs)
      }),
      _ == _
    ) (initialApproximation)
    
  }
  
}