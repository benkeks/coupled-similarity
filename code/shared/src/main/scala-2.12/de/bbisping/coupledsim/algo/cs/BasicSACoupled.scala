package de.bbisping.coupledsim.algo.cs

import de.bbisping.coupledsim.ts.TransitionSystem
import de.bbisping.coupledsim.util.Relation
import de.bbisping.coupledsim.util.Coloring
import de.bbisping.coupledsim.algo.AlgorithmLogging
import de.bbisping.coupledsim.ts.WeakTransitionSystem

/**
 * Basic similarity algorithm from [RT2010]
 * 
 * Adds Coupling to BasicSAWeak, experimental. crashes for some systems!!
 * 
 * */
class BasicSACoupled[S, A, L] (
    val ts: WeakTransitionSystem[S, A, L])
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
        val preB = ts.weakPre(b)
        val preRelB = ts.weakPre(relation.values(colorB) flatMap oldPartitions).withDefaultValue(Set())
        (colorC, c) <- oldPartitions
        val preRelC = (relation.values(colorC) flatMap oldPartitions)
        (a, preBA) <- preB
        val preRelBA = preRelB(a)
        if (c exists preBA) &&
           (preRelC exists (!preRelBA(_)))
      } yield (a, b, preBA, preRelBA)
      
      // only use the first splitter for now (in accordance with RT2010)
      for {
        (sA, b, preBSA, sPreRelBSA) <- bSplitters.headOption
      } {
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
        logRelation(Relation.fromColoringPartitionRelation(partition, relation), "sim splitter" + bSplitters.head.toString)
      }
      
      if (bSplitters.nonEmpty) {
        true
      } else {
        // This tries to partition by coupling
        
        val oldPartitions = partition.partitions.withDefaultValue(Set())
        val bCouplingSplitters = for {
          (colorB, b) <- oldPartitions
          val relB = relation.values(colorB) flatMap oldPartitions
          val preRelBInv = (relation.valuesInverse(colorB) flatMap oldPartitions) flatMap ts.silentReachableInverse
          if (relB exists (!preRelBInv(_)))
        } yield (b, relB, preRelBInv)
        
        for {
          (b, relB, preRelBInv) <- bCouplingSplitters.headOption
        } {
          val pivot = partition.freshColor()
          partition = partition.split(preRelBInv)
          
          val newPartitions =  partition.partitions.withDefaultValue(Set())
          val relUpdate = for {
            (colorC, c) <- newPartitions
          } yield {
            val colorParentC = if (colorC >= pivot) colorC - pivot else colorC
            val relC1 = for {
              (colorD, d) <- newPartitions.toSet
              if d subsetOf (relation.values(colorParentC) flatMap oldPartitions)
            } yield (colorD, d)
            
            if (c == b) {
              (colorC, (relC1 filter ((_._2 subsetOf preRelBInv))) map (_._1))
            } else {
              (colorC, relC1 map (_._1))
            }
          }
          relation = (new Relation(relUpdate))
          
          if (pivot > 1024*1024) {
            // try to use only a reasonable part of the number space for colors
            val (newPart, map) = partition.normalizeReturnMap()
            partition = newPart
            val newRelation = for {
              (p, q) <- relation.tupleSet
            } yield (map(p), map(q))
            relation = new Relation(newRelation)
          }
          
          logRelation(Relation.fromColoringPartitionRelation(partition, relation), "cs splitter" + bCouplingSplitters.head.toString + " of " + bCouplingSplitters.size)
        }
        
        bCouplingSplitters.nonEmpty
      }
    }) {
      
      
    }
    
    Relation.fromColoringPartitionRelation(partition, relation)
  }
}