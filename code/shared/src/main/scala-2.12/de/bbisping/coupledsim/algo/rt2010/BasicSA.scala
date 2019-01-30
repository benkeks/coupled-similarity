package de.bbisping.coupledsim.algo.rt2010

import de.bbisping.coupledsim.ts.TransitionSystem
import de.bbisping.coupledsim.util.Relation
import de.bbisping.coupledsim.util.Coloring
import de.bbisping.coupledsim.algo.AlgorithmLogging

/**
 * Basic similarity algorithm from [RT2010]
 * 
 * @note only considers action labels for now.
 * 
 * */

class BasicSA[S, A, L] (
    val ts: TransitionSystem[S, A, L])
  extends AlgorithmLogging[S, A, L] {
  
  def compute() = {    
    
    val labelColors = {
      val parts = for {
        (_, s) <- ts.nodesByLabel
      } yield s
      Coloring.fromPartition(parts.toSet)
    }
    
    val actionColors =
      Coloring.fromPartition(ts.actions.map(Set(_)).toSet)
    
    // partition relation pair (aka <P,Rel>)
    var partition = labelColors
    var relation = new Relation[Coloring.Color](labelColors.universe map (c => (c,c)))
    
    while ({
      // this is a modification of BasicSA to use a whole signature of splitters
      val oldPartitions = partition.partitions.withDefaultValue(Set())
      val bSplitters = for {
        (colorB, b) <- oldPartitions
        val preB = ts.pre(b)
        val preRelB = ts.pre(relation.values(colorB) flatMap oldPartitions)
        (colorC, c) <- oldPartitions
        val preRelC = (relation.values(colorC) flatMap oldPartitions)
        (a, preBA) <- preB
        if (c exists preBA) &&
           (preRelC exists (!preRelB(a)(_)))
      } yield (a, b, preBA, preRelB(a))
      
      // only use the first splitter for now (in accordance with RT2010)
      for {
        (sA, b, preBSA, sPreRelBSA) <- bSplitters.headOption
      } {
        val pPrev = partition
        val pivot = partition.freshColor() // the splitting procedure will use freshColor as the offset between old and newly added "child" partitions.
        // so c1,c2 in partition.split(...) share a parent iff c1.color = c2.color or Abs(c1.color - c2.color) = pivot.
        partition = partition.split(sPreRelBSA)
        
        val newPartitions =  partition.partitions.withDefaultValue(Set())
        val relUpdate = for {
          (colorC, c) <- newPartitions
        } yield {
          val colorParentC = if (colorC >= pivot) colorC - pivot else colorC
          val relC1 = for {
            (colorD, d) <- newPartitions.toSet
            if d subsetOf (relation.values(colorParentC) flatMap oldPartitions)
          } yield (colorD, d)
          
          if (c exists preBSA) {
            (colorC, (relC1 filter (_._2 subsetOf sPreRelBSA)) map (_._1))
          } else {
            (colorC, relC1 map (_._1))
          }
        }
        relation = (new Relation(relUpdate))
        logRelation(Relation.fromColoringPartitionRelation(partition, relation), "splitter" + bSplitters.head.toString)
      }
      
      bSplitters.nonEmpty
    }) {}
    
    Relation.fromColoringPartitionRelation(partition, relation)
  }
}