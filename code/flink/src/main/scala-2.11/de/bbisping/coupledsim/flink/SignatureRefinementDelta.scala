package de.bbisping.coupledsim.flink

import de.bbisping.coupledsim.flink.CoupledSimulationFlink.Action
import de.bbisping.coupledsim.util.Coloring
import org.apache.flink.api.common.functions.FlatMapFunction
import org.apache.flink.api.scala.{DataSet, _}
import org.apache.flink.api.scala.utils.DataSetUtils
import org.apache.flink.graph.scala.Graph
import org.apache.flink.types.NullValue
import org.apache.flink.util.Collector

/**
  * Not yet working properly. (Because of instable hashes in graph circles)
  */
class SignatureRefinementDelta {

  import SignatureRefinement._

  type Signature = Set[(Coloring.Color, Coloring.Color)]

  def compute(
      ts: Graph[Int, NullValue, CoupledSimulationFlink.Action])
  : (DataSet[(Int, Coloring.Color)], DataSet[(Int, Set[(Coloring.Color, Coloring.Color)])]) = {

    val verts = ts.getVertexIds()

    val initialColoring: DataSet[(Int, Color)] = verts.map((_, Long.MinValue))

    val coloring = initialColoring.iterateDelta(initialColoring, CoupledSimulationFlink.MAX_ITERATIONS, Array(0)) { (currentColoring, lastChanges) =>

      // we only have to update predecessors of changed vertices
      val activeVertices: DataSet[Int] =
        (lastChanges join ts.getEdgeIds() where (v => v._1) equalTo 1) { (_, edge) => println(edge._1); edge._1 }.distinct

      val oldSignatures: DataSet[(Int, Color)] =
        (activeVertices join currentColoring where (v => v) equalTo 0) { (_, oldSig) => oldSig }

      // the edges originating from active vertices have to be considered to compute new signatures
      val activeEdges: DataSet[(Int, Int, Action)] =
        (activeVertices join ts.getEdgesAsTuple3() where (v => v) equalTo 0) { (_, edge) => edge }

      val signatureEdges: DataSet[(Int, (Color, Color))] =
        (activeEdges join currentColoring where 1 equalTo 0) { (edge, color) =>
          (edge._1, (edge._3, color._2))
      }

      val signatureUpdates: DataSet[(Int, Color)] =
        signatureEdges.groupBy(0).reduceGroup { g =>
          val head = g.next
          (head._1, longHashing(g.map(_._2).toSet + head._2))
        }

      val vertexColorComparison: DataSet[(Int, Color, Color)] =
        (signatureUpdates join currentColoring where 0 equalTo 0) { (newSig, oldSig) =>
          (newSig._1, newSig._2, oldSig._2)
      }

      val reallyUpdatedVertices = vertexColorComparison flatMap new FlatMapFunction[(Int, Color, Color), (Int, Color)] {
        def flatMap(change: (Int, Color, Color),
                    out: Collector[(Int, Color)]): Unit = change match {
          case (id: Int, newColor: Color, oldColor: Color) =>
            if (newColor != oldColor) {
              println(id, oldColor, newColor)
              out.collect((id, newColor))
            }
        }
      }
//
//
//      filter new FilterFunction[(Int, Color, Color)] {
//        def filter(update: (Int, Color, Color)): Boolean = update match {
//          case (id: Int, newColor: Color, oldColor: Color) => newColor != oldColor
//        }
//      }
//
//      val reallyUpdatedVertices = realUpdates map (change => change._1)

      (reallyUpdatedVertices, reallyUpdatedVertices)
    }
/*
    val coloring = initialColoring.iterateWithTermination(CoupledSimulationFlink.MAX_ITERATIONS) { coloring =>

      //val oldSigMaxId: DataSet[Color] = coloring.max(1).map(_._2)
      //val oldSigs: DataSet[(Int, Int)] = coloring.map(_._2).distinct.map(_ => (1,1))
      val oldSigCount: DataSet[(Int, Int)] = coloring.map(_._2).distinct.map(_ => (1,1)).sum(0)
      
      val signatureEdges: DataSet[(Int, (Color, Color))] = ts.getEdgesAsTuple3().join(coloring).where(1).equalTo(0) {
        (edge, color) => (edge._1, (edge._3.toInt, color._2))
      }
      val signatures: DataSet[(Int, Color)] =
        signatureEdges.groupBy(0).reduceGroup { g =>
          val head = g.next
          (head._1, longHashing((g.map(_._2)).toSet + head._2))
        }
/*
      // defragment colors (new IDs on LHS)
      val signatureColors: DataSet[(Color, Color)] =
        DataSetUtils(signatures.map(s => s._2).distinct).zipWithIndex

      val verticesColored: DataSet[(Int, Color)] =
        (signatures join signatureColors).where(1).equalTo(1) {
          (vertSig, sigId) => (vertSig._1, sigId._1)
        }*/

      // new colors for the vertices, still keeping color for vertices without out-edges!
      val newColoring: DataSet[(Int, Color)] = coloring.leftOuterJoin(signatures)
        .where(0).equalTo(0) { (oldColoring, newColor) =>
        if (newColor == null) (oldColoring._1, Long.MinValue) else newColor
      }

      //val newSigMaxId: DataSet[Color] = newColoring.max(1).map(_._2)
      val newSigCount: DataSet[(Int, Int)] = newColoring.map(_._2).distinct.map(_ => (1,1)).sum(0)

//      val terminationSet = (oldSigMaxId cross newSigMaxId) filter { on =>
//        println(Console.GREEN + " {Old Count, new Count} " + on)
//        on._1 < on._2
//      }
      val terminationSet = (oldSigCount cross newSigCount).filter(on => on._1._1 < on._2._1)

      (newColoring, terminationSet)
    }
*/
    val compactColorIds: DataSet[(Long, Color)] = DataSetUtils(coloring.map(_._2).distinct).zipWithIndex
    val compactColoring = (coloring join compactColorIds).where(1).equalTo(1) {
      (vertSig, sigId) => (vertSig._1, sigId._1.toInt)
    }

    // recompute the last signatures
    val signatureEdges: DataSet[(Int, (Coloring.Color, Coloring.Color))] = ts.getEdgesAsTuple3().join(compactColoring).where(1).equalTo(0) {
      (edge, color) => (edge._1, (edge._3.toInt, color._2))
    }
    val signatures: DataSet[(Int, Set[(Coloring.Color, Coloring.Color)])] = signatureEdges.groupBy(0).reduceGroup { g =>
      val head = g.next()
      (head._1, g.map(_._2).toSet + head._2)
    }
    
    (compactColoring, signatures)
  }
  
}

