package de.bbisping.coupledsim.algo

import scala.annotation.migration

import de.bbisping.coupledsim.ts.TransitionSystem
import de.bbisping.coupledsim.util.FixedPoint
import de.bbisping.coupledsim.util.Relation

/** remove transitions where source and target both lie in a certain set. */
class RemoveEndoTransitions[S, A, L] (
    ts: TransitionSystem[S, A, L],
    transitiveStates: Set[S]) {
  
  def compute() = {
    ts.step
//    val newTrans = for {
//      (a, b) <- ts.step.tupleSet
//      if !(transitiveStates contains a) || !(transitiveStates contains b)
//    } yield (a, b)
//    new Relation(newTrans)
  }
  
}