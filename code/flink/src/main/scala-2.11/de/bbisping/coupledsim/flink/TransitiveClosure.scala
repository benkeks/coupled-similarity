package de.bbisping.coupledsim.flink

import org.apache.flink.api.common.typeinfo.TypeInformation
import org.apache.flink.api.scala.DataSet
import org.apache.flink.util.Collector

import scala.reflect.ClassTag


class TransitiveClosure[A] {
  
  def compute(steps: DataSet[(A, A)])
    (implicit evidence: TypeInformation[(A, A)], classTag: ClassTag[(A, A)])
  : DataSet[(A, A)] = {
    
    val closedSteps = steps.iterateDelta(steps, CoupledSimulationFlink.MAX_ITERATIONS, Array(0,1)) { (closedStepsPartial, deltaSteps) =>
      val newSteps: DataSet[(A, A)] = (deltaSteps join steps)
        .where(1).equalTo(0) { (step1: (A,A), step2: (A,A)) =>
          (step1._1, step2._2)
      }
      
      val reallyNewSteps: DataSet[(A, A)] = (newSteps coGroup closedStepsPartial)
        .where(0,1).equalTo(0,1).apply(fun = { (st1: Iterator[(A,A)], st2: Iterator[(A,A)], out: Collector[(A,A)]) => 
          if (st2.isEmpty) {
            for (st <- st1) out.collect(st)
          }
      })
      
      (reallyNewSteps, reallyNewSteps)
    }
    
    closedSteps
  }
  
}