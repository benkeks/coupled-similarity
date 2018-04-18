package de.bbisping.coupledsim.flink

import org.apache.flink.api.scala._
import org.apache.flink.api.scala.DataSet
import org.apache.flink.graph.scala.Graph
import org.apache.flink.types.NullValue
import de.bbisping.coupledsim.util.Coloring
import org.apache.flink.api.common.functions.FlatMapFunction
import org.apache.flink.util.Collector
import org.apache.flink.api.common.functions.FilterFunction
import org.apache.flink.api.common.functions.JoinFunction
import scala.reflect.ClassTag
import org.apache.flink.api.common.typeinfo.TypeInformation
import org.apache.flink.api.scala.utils.`package`.DataSetUtils


class SignatureRefinement {
  
  import CoupledSimulationFlink.Action
  
  type Signature = Set[(Coloring.Color, Coloring.Color)]
  
  def compute(
      ts: Graph[Int, NullValue, CoupledSimulationFlink.Action])
  : (DataSet[(Int, Coloring.Color)], DataSet[(Int, Set[(Coloring.Color, Coloring.Color)])]) = {
    
    val initialColoring: DataSet[(Int, Coloring.Color)] = ts.getVertexIds().map((_, 0))
    
    val coloring = initialColoring.iterateWithTermination(CoupledSimulationFlink.MAX_ITERATIONS) { coloring =>

      val oldSigs: DataSet[(Int, Int)] = coloring.map(_._2).distinct.map(s => (1,1))
      val oldSigCount: DataSet[(Int, Int)] = oldSigs.sum(0)
      
      val signatureEdges: DataSet[(Int, (Coloring.Color, Coloring.Color))] = ts.getEdgesAsTuple3().join(coloring).where(1).equalTo(0) {
        (edge, color) => (edge._1, (edge._3.toInt, color._2))
      }
      val signatures: DataSet[(Int, Set[(Coloring.Color, Coloring.Color)])] = signatureEdges.groupBy(0).reduceGroup { g =>
        val head = g.next()
        (head._1, g.map(_._2).toSet + head._2)
      }
      
      val newColoring: DataSet[(Int, Coloring.Color)] = coloring.leftOuterJoin(signatures)
        .where(0).equalTo(0) ((oldColoring, newSig) => if (newSig == null) oldColoring else (newSig._1, newSig._2.hashCode()))
      
      val newSigCount: DataSet[(Int, Int)] = newColoring.map(_._2).distinct.map(s => (1,1)).sum(0)
      
      val terminationSet = (oldSigCount cross newSigCount).filter(on => on._1._1 < on._2._1)
      
      (newColoring, terminationSet)
    }
    
    // recompute the last signatures
    val signatureEdges: DataSet[(Int, (Coloring.Color, Coloring.Color))] = ts.getEdgesAsTuple3().join(coloring).where(1).equalTo(0) {
      (edge, color) => (edge._1, (edge._3.toInt, color._2))
    }
    val signatures: DataSet[(Int, Set[(Coloring.Color, Coloring.Color)])] = signatureEdges.groupBy(0).reduceGroup { g =>
      val head = g.next()
      (head._1, g.map(_._2).toSet + head._2)
    }
    
    (coloring, signatures)
  }
  
}