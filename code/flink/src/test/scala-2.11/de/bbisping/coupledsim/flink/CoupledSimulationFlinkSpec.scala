package de.bbisping.coupledsim.flink

import scala.io.Source

import org.apache.flink.api.scala.ExecutionEnvironment
import org.scalatest.FunSpec
import org.scalatest.Inspectors.forAll
import org.scalatest.Matchers.be
import org.scalatest.Matchers.convertToAnyShouldWrapper
import org.scalatest.Matchers.empty
import org.scalatest.concurrent.TimeLimits
import org.scalatest.time.SpanSugar._

import de.bbisping.coupledsim.algo.cs.FixedPointCoupledSimilarity
import de.bbisping.coupledsim.ts.DirectTSImporter

class CoupledSimulationFlinkSpec extends FunSpec with TimeLimits {
  
  val smallSamples: Seq[String] = CoupledSimulationFlinkBenchmark.smallSamples
  
  val vltsSamplesSmall: Seq[String] = CoupledSimulationFlinkBenchmark.vltsSamplesSmall
    
  val vltsSamplesMedium: Seq[String] = CoupledSimulationFlinkBenchmark.vltsSamplesMedium
    
  val env: ExecutionEnvironment = ExecutionEnvironment.getExecutionEnvironment
  
  describe("The computed CS relation") {
    forAll(smallSamples) { sample =>
      describe("for sample " + sample) {
        val src = Source.fromFile(sample).mkString
        println("\nTEST: " + Console.BLUE + sample + Console.RESET)
        val ts = new DirectTSImporter(src).result()
        val rel = new FixedPointCoupledSimilarity(ts).compute()

        val cs = CoupledSimulationFlink.executeAlgorithm(env, cfgPath = sample, cfgReturnRelation = true).relation.get

        it("should be sound") {
          (cs.tupleSet diff rel.tupleSet) should be (empty)
        }

        it("should be complete") {
          (rel.tupleSet diff cs.tupleSet) should be (empty)
        }
      }
    }
    
    forAll(vltsSamplesSmall) { sample =>
      describe("for sample " + sample) {
        println("\n" + Console.BLUE + sample + Console.RESET)

        it("should be computed in a reasonable amount of time and be sound (by self-check)") {
          failAfter(180 seconds) {
            val cs = CoupledSimulationFlink.executeAlgorithm(env, cfgPath = sample, cfgReturnRelation = true, cfgCheckSoundness = true)
            cs.sound.get shouldEqual true
          }
        }
      }
    }

    forAll(vltsSamplesMedium) { sample =>
      describe("for sample " + sample) {
        it("should be computed in a reasonable amount of time") {
          failAfter(360 seconds) {
            CoupledSimulationFlink.executeAlgorithm(env, cfgPath = sample)
          }
        }
      }
    }
  }
  
}