package de.bbisping.coupledsim.flink

import java.lang.{Long => JavaLong}

import de.bbisping.coupledsim.util.Coloring
import org.apache.flink.api.scala.{DataSet, _}
import org.apache.flink.api.scala.utils.DataSetUtils
import org.apache.flink.graph.scala.Graph
import org.apache.flink.types.NullValue


class SignatureRefinement {

  import SignatureRefinement._

  type Signature = Set[(Coloring.Color, Coloring.Color)]

  def compute(
      ts: Graph[Int, NullValue, CoupledSimulationFlink.Action])
  : (DataSet[(Int, Coloring.Color)], DataSet[(Int, Set[(Coloring.Color, Coloring.Color)])]) = {

    val verts = ts.getVertexIds()

    val initialColoring: DataSet[(Int, Color)] = verts.map((_, Long.MinValue))

    val coloring = initialColoring.iterateWithTermination(CoupledSimulationFlink.MAX_ITERATIONS) { coloring =>

      val oldSigCount: DataSet[Tuple1[Int]] = coloring.map(_._2).distinct.map(_ => Tuple1(1)).sum(0)
      
      val signatureEdges: DataSet[(Int, (Color, Color))] = ts.getEdgesAsTuple3().join(coloring).where(1).equalTo(0) {
        (edge, color) => (edge._1, (edge._3.toInt, color._2))
      }
      val signatures: DataSet[(Int, Color)] =
        signatureEdges.groupBy(0).reduceGroup { g =>
          val head = g.next
          (head._1, longHashing(g.map(_._2).toSet + head._2))
        }

      // new colors for the vertices, still keeping color for vertices without out-edges!
      val newColoring: DataSet[(Int, Color)] = coloring.leftOuterJoin(signatures)
        .where(0).equalTo(0) { (oldColoring, newColor) =>
        if (newColor == null) (oldColoring._1, Long.MinValue) else newColor
      }

      val newSigCount: DataSet[Tuple1[Int]] = newColoring.map(_._2).distinct.map(_ => Tuple1(1)).sum(0)

      val terminationSet = (oldSigCount cross newSigCount).filter(on => on._1._1 < on._2._1)

      (newColoring, terminationSet)
    }

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

object SignatureRefinement {

  type Color = Long

  class FullSignature(entries: Set[(Coloring.Color, Coloring.Color)]) extends Ordered[FullSignature] {
    lazy private val str = entries.mkString(",")

    def compare(that: FullSignature): Int = str compare that.str
  }


  def longHashing(xs: TraversableOnce[Any]) = {
    // adapted from https://github.com/scala/scala/blob/v2.12.5/src/library/scala/util/hashing/MurmurHash3.scala
    var a, b, n = 0L
    var c = 1L
    xs foreach { x =>
      val h = x.hashCode
      a += h
      b ^= h
      if (h != 0) c *= h
      n += 1
    }
    var h = 23L
    h = mix(h, a)
    h = mix(h, b)
    h = mixLast(h, c)
    finalizeHash(h, n)
  }

  /** Mix in a block of data into an intermediate hash value. */
  final def mix(hash: Long, data: Long): Long = {
    var h = mixLast(hash, data)
    h = JavaLong.rotateLeft(h, 13)  //Integer.rotateLeft(h, 13)
    h * 5 + 0xe6546b64
  }

  /** May optionally be used as the last mixing step. Is a little bit faster than mix,
    *  as it does no further mixing of the resulting hash. For the last element this is not
    *  necessary as the hash is thoroughly mixed during finalization anyway. */
  final def mixLast(hash: Long, data: Long): Long = {
    var k = data

    k *= 0xcc9e2d51
    k = JavaLong.rotateLeft(k, 15)
    k *= 0x1b873593

    hash ^ k
  }

  /** Finalize a hash to incorporate the length and make sure all bits avalanche. */
  final def finalizeHash(hash: Long, length: Long): Long = avalanche(hash ^ length)

  /** Force all bits of the hash to avalanche. Used for finalizing the hash. */
  private final def avalanche(hash: Long): Long = {
    var h = hash

    h ^= h >>> 16
    h *= 0x85ebca6b
    h ^= h >>> 13
    h *= 0xc2b2ae35
    h ^= h >>> 16

    h
  }
}