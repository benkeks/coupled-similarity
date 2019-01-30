package de.bbisping.coupledsim.algo

import scala.annotation.migration

import de.bbisping.coupledsim.ts.TransitionSystem
import de.bbisping.coupledsim.util.FixedPoint
import de.bbisping.coupledsim.util.Relation

/** for a class of nodes, splits each node into a group of nodes with one deterministic node for each original outgoing edge 
 *  
 * For example splitting a:
 * 
 * 0 --> a --> b  ~>  0 --> a --> b
 *        `-> c        `-> a --> c
 * 
 * For now, this is only meant to work if the nodes to be deterministified are not direct neighbors of one another.
 *
 * */
class NaiveDeterminismAdder[S, A, L] (
    ts: TransitionSystem[S, A, L],
    nodeCopyLabelFactory: ((S, Int) => S),
    determinismNeeded: Set[S]) {
  
  def compute() = {
//    // stop-nodes are allowed to survive ;)
//    val oldNodes = (determinismNeeded intersect ts.nodes).filter(ts.step.values(_).nonEmpty)
//    
//    val newNodeData = for {
//      oldNode <- oldNodes
//      (outNeighbor, i) <- ts.step.values(oldNode).zipWithIndex
//    } yield (nodeCopyLabelFactory(oldNode, i), oldNode, outNeighbor)
//    
//    val newNodes = for {
//      (node, oldNode, _) <- newNodeData
//    } yield (node, ts.labeling(oldNode))
//    
//    val newInTrans = for {
//      (node, oldNode, _) <- newNodeData
//      inNeighbor <- ts.step.valuesInverse(oldNode)
//    } yield (inNeighbor, node)
//    
//    val newOutTrans = for {
//      (node, _, outNeighbor) <- newNodeData
//    } yield (node, outNeighbor)
//    
//    val newSteps = ts.step removeKeys oldNodes merge new Relation(newInTrans ++ newOutTrans)
//    
//    val newLabeling = ts.labeling.filterKeys(!oldNodes.contains(_)) ++ newNodes
//    
//    TransitionSystem(newSteps, newLabeling)
  }
  
}