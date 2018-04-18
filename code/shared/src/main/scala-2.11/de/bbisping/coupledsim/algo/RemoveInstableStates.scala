package de.bbisping.coupledsim.algo

import de.bbisping.coupledsim.ts.TransitionSystem
import de.bbisping.coupledsim.util.FixedPoint
import de.bbisping.coupledsim.ts.WeakTransitionSystem
import de.bbisping.coupledsim.util.LabeledRelation

/** removes transitions leading to instable non-divergent states.
 *  (assumes that a transitive closure has been computed before, but no reflexive closure,
 *  so that exactly the reflexive states are divergent.)*/
class RemoveInstableStates[S, A, L] (
    ts: WeakTransitionSystem[S, A, L]) {
  
  def compute() = {
    val instableNDStates = for {
      p <- ts.nodes
      val enabledSilent = ts.enabled(p) intersect ts.silentActions
      if enabledSilent.nonEmpty                    // instable state
      if !(ts.post(p, enabledSilent) contains p)   // non-divergent state
    } yield p
    
    val newTrans = for {
      (p1, a, p2) <- ts.step.tupleSet
      if !(instableNDStates contains p2)
    } yield (p1, a, p2)
    new LabeledRelation(newTrans)
  }
  
}