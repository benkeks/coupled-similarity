package de.bbisping.coupledsim.algo

import de.bbisping.coupledsim.ts.TransitionSystem
import de.bbisping.coupledsim.util.Partition

class PaigeTarjan[S, A, L](ts: TransitionSystem[S, A, L]) {
  
  def split(s: Set[S], p: Partition[S]) = {
//    for {
//      b <- p.parts
//      pre = ts.pre(s)
//      (b1, b2) = b partition pre
//    } yield List(b1, b2)
  }
  
}