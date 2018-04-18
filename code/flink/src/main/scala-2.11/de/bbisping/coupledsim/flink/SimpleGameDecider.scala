package de.bbisping.coupledsim.flink

import scala.reflect.ClassTag

import org.apache.flink.api.common.typeinfo.TypeInformation
import org.apache.flink.api.scala._
import org.apache.flink.api.scala.ExecutionEnvironment
import org.apache.flink.graph.scala.Graph
import org.apache.flink.types.NullValue
import org.apache.flink.graph.spargel.ScatterGatherConfiguration
import org.apache.flink.graph.spargel.ScatterFunction
import org.apache.flink.types.LongValue
import org.apache.flink.graph.EdgeDirection
import org.apache.flink.graph.Vertex
import org.apache.flink.graph.spargel.MessageIterator
import org.apache.flink.graph.spargel.GatherFunction

class SimpleGameDecider {
  
  import CoupledSimulationFlink.Action
  
  def compute(
      gameGraph: Graph[(CoupledSimulationFlink.Action, Int, Int), Int, NullValue],
      env: ExecutionEnvironment): Graph[(CoupledSimulationFlink.Action, Int, Int), Int, NullValue] = {
    implicit val tupleType = TypeInformation.of(classOf[((Action, Int, Int), Int)])
    implicit val tupleClassTag = ClassTag.apply(classOf[((Action, Int, Int), Int)])
    
    val successorCount = gameGraph.outDegrees().map(
        (nodeOut: ((Action, Int, Int), LongValue)) => nodeOut match {
        case ((v: (Action, Int, Int), d: LongValue)) => 
          val num = d.getValue.toInt
          (v, if (num == 0 && v._1 != CoupledSimulationGame.ATTACK) SimpleGameDecider.ATTACKER_WIN_MAGIC_NUMBER else num)
      }
    )
    
    val winningRegionComputationGraph: Graph[(Action, Int, Int), Int, NullValue] =
      Graph.fromTupleDataSet(successorCount, gameGraph.getEdgesAsTuple3, env)
        
    val propagate = new ScatterFunction[(Action, Int, Int), Int, Int, NullValue] {
      
    	override def sendMessages(vertex: Vertex[(Action, Int, Int), Int]) = {
    	  if (vertex.getValue == SimpleGameDecider.ATTACKER_WIN_MAGIC_NUMBER ) {
    	    val edges = getEdges.iterator()
    	    while (edges.hasNext) {
    	      val edge = edges.next
		      	sendMessageTo(edge.getSource, 1)
    	    }
    	  }
		  }
    }
    
    val propagateGather = new GatherFunction[(Action, Int, Int), Int, Int] {
      
    	override def updateVertex(vertex: Vertex[(Action, Int, Int), Int], inMessages: MessageIterator[Int]) = {
    		var value = vertex.getValue
    		
    		if (value != SimpleGameDecider.ATTACKER_WIN_MAGIC_NUMBER) {
    		  var count = 0
      		while (inMessages.hasNext) {
      		  val msg = inMessages.next
      		  count += 1
      		}
      		
      		if (count > 0 && vertex.getId._1 == CoupledSimulationGame.ATTACK || count >= value ) {
      		  value = SimpleGameDecider.ATTACKER_WIN_MAGIC_NUMBER
      		} else {
      		  value -= count
      		}
      		
      		if (value < vertex.getValue) {
      		  setNewVertexValue(value)
      		}
    		}
    	}
    }
    
    val propagateCfg = new ScatterGatherConfiguration
    propagateCfg.setDirection(EdgeDirection.IN)
    
    winningRegionComputationGraph
      .runScatterGatherIteration(propagate, propagateGather, CoupledSimulationFlink.MAX_ITERATIONS, propagateCfg)
  }
  
}

object SimpleGameDecider {
  val ATTACKER_WIN_MAGIC_NUMBER = -1
}
