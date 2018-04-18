package de.bbisping.coupledsim.algo.rt2010

import de.bbisping.coupledsim.ts.TransitionSystem
import de.bbisping.coupledsim.util.Relation

/**
 * Refined similarity algorithm from [RT2010]
 * 
 * @note only considers action labels for now.
 * 
 * */

class RefinedSimilarity[S, A, L] (
    val ts: TransitionSystem[S, A, L]) {
  
  def compute() = {
    val prevCand = for {
      s1 <- ts.nodes
      s2 <- ts.nodes
    } yield (s1, s2)
    
    val initialCandidates = for {
      s1 <- ts.nodes
      s2 <- ts.nodes
      if ts.enabled(s1) subsetOf ts.enabled(s2)
    } yield (s1, s2)
    
    var prevSim = prevCand groupBy (_._1) mapValues(_.map(_._2))
    var sim = initialCandidates groupBy (_._1) mapValues(_.map(_._2))
    // I don't need special treatment of deadlocks like RT2010 because of action based computation of initial candidates.
    
    while ({
      val vOpt = sim find {
        case (v, simv) => prevSim(v).size != simv.size // size comparison suffices because of [RT2010, Inv 1]
      }
      
      for ((v, simv) <- vOpt) {
        val oldPrevSim = prevSim(v)
        prevSim = prevSim updated(v, simv)
        for ((a, uu) <- ts.pre(oldPrevSim)) {
          val remove = uu -- ts.pre(sim(v), a)
          for {
            u <- ts.pre(v, a) 
          } {
            sim = sim updated (u, sim(u) -- remove)
          }
        }
      }
      
      vOpt.nonEmpty
    }) {}
    
    new Relation(sim)
  }
}