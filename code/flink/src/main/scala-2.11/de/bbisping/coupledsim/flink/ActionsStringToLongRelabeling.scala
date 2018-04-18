package de.bbisping.coupledsim.flink

import org.apache.flink.api.scala._
import org.apache.flink.graph.scala.Graph
import org.apache.flink.api.scala.utils.`package`.DataSetUtils
import org.apache.flink.api.scala.DataSet
import org.apache.flink.types.NullValue

class ActionsStringToLongRelabeling(ts: Graph[Int, NullValue, String]) {
  
  def compute(env: ExecutionEnvironment, tauStr: String, tau: Long): (Graph[Int, NullValue, Long], DataSet[(Long, String)]) = {
    val stringLabeledEdges = ts.getEdgesAsTuple3()
    
    val actions: DataSet[String] = stringLabeledEdges.map(_._3).distinct()
    val preliminaryActionIds: DataSet[(Long, String)] = DataSetUtils(actions).zipWithIndex//.zipWithUniqueId
    val actionIds: DataSet[(Long, String)] =
      preliminaryActionIds map ({ case ((id, name)) =>
        if (name == tauStr) {
          (tau, name)
        } else {
          (id + tau + 10, name)
        }
    }: ((Long, String)) => (Long, String))
    
    val relabeledEdges: DataSet[(Int, Int, Long)] =
      (stringLabeledEdges join actionIds)
      .where(2).equalTo(1) { (edge, actionId) =>
        (edge._1, edge._2, actionId._1)
    }
    
    (Graph.fromTupleDataSet(ts.getVerticesAsTuple2(), relabeledEdges, env), actionIds)
  }
  
}