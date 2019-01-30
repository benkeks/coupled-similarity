package de.bbisping.coupledsim.algo.transform

import scala.annotation.migration
import de.bbisping.coupledsim.ts.TransitionSystem
import de.bbisping.coupledsim.util.LabeledRelation
import de.bbisping.coupledsim.ts.DivergenceInformation
import de.bbisping.coupledsim.ts.WeakTransitionSystem

/** [CH1993, p. 15]
 *  (understanding the definition to have side effects (globally updating -->_T etc.)) */
class AGraphConstruction[S, A, L] (
    ts: WeakTransitionSystem[S, A, L] with DivergenceInformation[S],
    newState: (WeakTransitionSystem[S, A, L], Set[A], Boolean) => (S, L) 
    ) {
  
  // environment E for new states
  protected val newStates: collection.mutable.Map[(Set[S], Boolean), S] = collection.mutable.Map()
  
  /**
   * assumes that tau closure has already been built  
   */
  def compute(initial: S) = {
    build(new WeakTransitionSystem(LabeledRelation(), Map(), ts.silentActions), Set(initial), true)
  }
  
  def build(pats: WeakTransitionSystem[S, A, L] , activeStates: Set[S], convergent: Boolean): (WeakTransitionSystem[S, A, L], S) = {
    
    // reading S^tau as S^eta
    val tauStates = for {
      s <- activeStates
      sR <- ts.silentReachable(s)
    } yield sR
    
    newStates.get(tauStates, convergent) match {
      // if E(<S^tau, b>) exists then return <<T, Act, -->_T>, E(<S^tau, b>)>
      case Some(tsc) => 
        (pats, tsc)
      // else
      case None =>
        // c
        val c = convergent && tauStates.forall(!ts.diverges(_))
        // acc
        val accepting = if (c) { 
          for {
            p <- tauStates
            enabled = ts.enabled(p)
            if !enabled.exists(ts.silentActions)
            a <- enabled
          } yield a
        } else {
          Set[A]()
        }
        // t := newstate(acc, c)
        val (t, label) = newState(pats, accepting, c)
        
        // E := E[<S^tau,c> |-> t]
        newStates((tauStates, c)) = t
        
        // T := T union {t}
        var nodeLabeling = pats.nodeLabeling.updated(t, label)
        
        var step = pats.step 
        
        // reading s as p in ... | ? p : S^tau . s -->^a }
        val enabledVisibleActions = for {
          p <- tauStates
          a <- ts.enabled(p)
          if !ts.silentActions(a)
        } yield a
        
        for (a <- enabledVisibleActions) {
          // S_a
          val aStates = ts.post(tauStates, a)
          val (l, t1) = build(new WeakTransitionSystem(step, nodeLabeling, ts.silentActions), aStates, c)
          
          //TODO: change this to mutable data structures to faithfully capture the algorithm from [CH1993, p. 15] without complexity blow up..
          step = new LabeledRelation(step.tupleSet ++ l.step.tupleSet + ((t, a , t1))) 
          nodeLabeling ++= l.nodeLabeling
        }
        
        (new WeakTransitionSystem(step, nodeLabeling, ts.silentActions), t)
    }
  }
}