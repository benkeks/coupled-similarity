package de.bbisping.coupledsim.algo.rt2010

import de.bbisping.coupledsim.ts.TransitionSystem
import de.bbisping.coupledsim.util.Relation
import de.bbisping.coupledsim.util.Coloring
import de.bbisping.coupledsim.algo.AlgorithmLogging

/**
 * RefinedSA similarity algorithm from [RT2010]
 * 
 * @note only considers action labels for now.
 * 
 * */

class RefinedSA[S, A, L] (
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
    
    val initRel = relation
    val initPart = partition
    logRelation(Relation.fromColoringPartitionRelation(initPart, initRel), "intial")
    
    var prePrevRel = {
      for {
        b <- partition.universe
        a <- ts.actions
      } yield ((b, a), ts.nodes)//partition.universe ?
    }.toMap
    
    while ({
      val oldPartitions = partition.partitions.withDefaultValue(Set())
//      val bSplitters = for {
//        (colorB, b) <- oldPartitions
//        val preRelB = ts.pre(relation.values(colorB) flatMap oldPartitions)
//        (a, preRelBA) <- preRelB
//        val prePrevRelBA = prePrevRel(colorB, a)
//        val remove = prePrevRelBA -- preRelBA
//        if remove.nonEmpty
//      } yield (a, b, colorB, preRelBA, prePrevRelBA, remove)
      val bSplitters = oldPartitions collectFirst (Function.unlift({
        case (colorB, b) =>
          val preRelB = ts.pre(relation.values(colorB) flatMap oldPartitions)
          for {
            (a, preRelBA) <- preRelB find {
              case (a, preRelBA) =>
                val prePrevRelBA = prePrevRel(colorB, a)
                val remove = prePrevRelBA -- preRelBA
                remove.nonEmpty
            }
            val prePrevRelBA = prePrevRel(colorB, a)
          } yield (a, b, colorB, preRelBA, prePrevRelBA, prePrevRelBA -- preRelBA)
      }))
      for {
        (a, b, colorB, preRelBA, prePrevRelBA, remove) <- bSplitters
      } {
        val newPrePrevRelBA = preRelBA
        prePrevRel = prePrevRel updated ((colorB, a), newPrePrevRelBA)
        val pivot = partition.freshColor() // the splitting procedure will use freshColor as the offset between old and newly added "child" partitions.
        // so c1,c2 in partition.split(...) share a parent iff c1.color = c2.color or Abs(c1.color - c2.color) = pivot.
        partition = partition.split(newPrePrevRelBA)
        
        val preBA = ts.pre(b,a)
        
        val newPartitions =  partition.partitions.withDefaultValue(Set())
        val relUpdate = for {
          (colorC, c) <- newPartitions
        } yield {
          val colorParentC = if (colorC >= pivot) colorC - pivot else colorC
          val relC1 = for {
            (colorD, d) <- newPartitions.toSet
            if d subsetOf (relation.values(colorParentC) flatMap oldPartitions)
          } yield (colorD, d)
          
          if (c exists preBA) {
            (colorC, (relC1 filter (_._2 subsetOf preRelBA)) map (_._1))
          } else {
            (colorC, relC1 map (_._1))
          }
        }
        relation = new Relation(relUpdate)
        
        val prePrevRelUpdate = for {
          (colorC, c) <- newPartitions
          val colorParentC = if (colorC >= pivot) colorC - pivot else colorC
          action <- ts.actions
        } yield ((colorC, action), prePrevRel(colorParentC, action))
        prePrevRel = prePrevRelUpdate
        
        logRelation(Relation.fromColoringPartitionRelation(partition, relation), "splitter" + bSplitters.head.toString)
      }
      
      bSplitters.nonEmpty
    }) {}
    
    Relation.fromColoringPartitionRelation(partition, relation)
  }
}