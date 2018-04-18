package de.bbisping.coupledsim.algo.rt2010

import de.bbisping.coupledsim.ts.TransitionSystem
import de.bbisping.coupledsim.util.Relation
import de.bbisping.coupledsim.algo.AlgorithmLogging

/**
 * Simplest similarity algorithm from [RT2010]
 * 
 * @note only considers action labels for now.
 * 
 * */

class SchematicSimilarity[S, A, L] (
    val ts: TransitionSystem[S, A, L])
  extends AlgorithmLogging[S, A, L] {
  
  def compute() = {
    val initialCandidates = for {
      s1 <- ts.nodes
      s2 <- ts.nodes
      if ts.enabled(s1) subsetOf ts.enabled(s2)
    } yield (s1, s2)
    
    var sim = new Relation[S](initialCandidates)
    logRelation(sim, "initial candidates")
    
    while ({
      val delCand = sim.rep collect {
        case (u, ww) => ww collect {
          case w if ts.post(u).exists {
            case (a, vv) => vv.exists { v =>
              val vsim = sim.values(v)
              ! ( ts.post(w, a) exists (vsim contains _) )
            }
          } => (u, w)
        }
      } flatten
      
      if (delCand.isEmpty) {
        false
      } else {
        val dcs = delCand.toSet
        sim = sim.filter((s1, s2) => !dcs.contains(s1, s2))
        logRelation(sim, "remove: " + dcs.mkString(", "))
        true
      }
    }) {}
    
    sim
  }
}