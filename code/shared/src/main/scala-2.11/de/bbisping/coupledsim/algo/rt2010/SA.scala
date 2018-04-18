package de.bbisping.coupledsim.algo.rt2010

import de.bbisping.coupledsim.ts.TransitionSystem
import de.bbisping.coupledsim.util.Relation
import de.bbisping.coupledsim.util.Coloring
import de.bbisping.coupledsim.algo.AlgorithmLogging

/**
 *SA similarity algorithm from [RT2010]
 * 
 * this experimental re-implementation presumably is not yet correct. don't use it!
 * 
 * @note only considers action labels for now.
 * 
 * */

class SA[S, A, L] (
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
    
    var remove = {
      for {
        b <- partition.universe
        a <- ts.actions
        val preRelBA = ts.pre(relation.values(b) flatMap partition.partitions.withDefaultValue(Set()), a)
      } yield ((b, a), ts.nodes -- preRelBA)
    }.toMap
    
    while ({
      
      val pickedBA = remove.find (_._2.nonEmpty)
      
      for {
        ((colorB, a), removeBA) <- pickedBA
      } {
        remove = remove updated ((colorB, a), Set())
        
        val oldPartitions = partition.partitions.withDefaultValue(Set())
        
        val preBA = ts.pre(oldPartitions(colorB),a)
        
        val pivot = partition.freshColor()
        
        partition = partition.split(removeBA)
        
        val newPartitions =  partition.partitions.withDefaultValue(Set())
        
        val removeUpdate = for {
          (colorC, c) <- newPartitions
          val colorParentC = if (colorC >= pivot) colorC - pivot else colorC
          action <- ts.actions
        } yield ((colorC, action), remove(colorParentC, action))
        remove = removeUpdate
        
        val relUpdate1 = for {
          (colorC, c) <- newPartitions
          val colorParentC = if (colorC >= pivot) colorC - pivot else colorC
        } yield (colorC, {
          for {
            (colorD, d) <- newPartitions.toSet
            if d subsetOf (relation.values(colorParentC) flatMap oldPartitions)
          } yield (colorD)
        })
        relation = new Relation(relUpdate1)
        
        val removeList = (newPartitions filter {case (colorD, d) => d subsetOf removeBA}).toSet
        
        for {
          (colorC, c) <- newPartitions
          if c exists preBA
          (colorD, d) <- removeList
          val relC =  for {
            c <- relation.values(colorC)
          } yield (c,newPartitions(c))
          if relC contains (colorD, d)
        } {
          relation = relation - (colorC, colorD)
          for {
            (action, ss) <- ts.pre(d)
            s <- ss
            if !(ts.pre(relation.values(colorC) flatMap newPartitions, action) contains s)
          } {
            val k = (colorC, action)
            remove = remove updated (k, remove.getOrElse(k, Set()) + s)
          }
        }
      }
      val logRel = relation
      val logPart = partition
      logRelation(Relation.fromColoringPartitionRelation(logPart, logRel), "splitter" + pickedBA.toString)
      
      pickedBA.nonEmpty
    }) {}
    
    Relation.fromColoringPartitionRelation(partition, relation)
  }
}