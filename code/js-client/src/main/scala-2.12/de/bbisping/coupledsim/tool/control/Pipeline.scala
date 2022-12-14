package de.bbisping.coupledsim.tool.control

import de.bbisping.coupledsim.tool.arch.Action
import de.bbisping.coupledsim.tool.arch.Control

class Pipeline(val main: Control) extends ModelComponent {
  
  var pipelineSource = Array[String]()
  var operations = Map[String, StructureOperation]()
  var currentStep = 0
  
  def changePipeline(code: String) = {
    pipelineSource = code.split("\n")
  }
  
  def runPipeline() = {
  }
  
  def stepPipeline() = {
    println("pipeline step")
    if (pipelineSource.length <= currentStep) {
      false
    } else {
      val currentLine = pipelineSource(currentStep).trim()
      val operation = operations.get(currentLine)
      
      for (
        op <- operation
      ) {
        main.dispatchAction(Structure.StructureCallOperation(op.slug))
      }
      
      setStep(currentStep + 1)
      
      operation.isDefined
    }
  }
  
  def resetPipeline() = {
    setStep(0)
  }
  
  def setStep(step: Int) = {
    currentStep = step
    broadcast(Pipeline.PipelineStatusChange(List(Pipeline.CurrentLine(currentStep))))
  }
  
  def notify(change: ModelComponent.Change) = change match {
    case Structure.StructureOperationsChanged(ops) =>
      operations = ops toMap
    case Structure.StructureChange(_) =>
      resetPipeline()
    case _ => 
  }
}

object Pipeline {
  
  abstract class LineInfo(line: Int)
  case class CurrentLine(line: Int) extends LineInfo(line)
  
  case class PipelineStatusChange(pipelineStatus: List[LineInfo]) extends ModelComponent.Change
  
  abstract sealed class PipelineAction extends Action {
    override def implement(target: ModelComponent): Boolean = target match {
      case s: Pipeline => 
        implementPipeline(s)
      case _ =>
        false
    }
    
    def implementPipeline(pipeline: Pipeline): Boolean
  }
  
  case class LoadPipeline(code: String) extends PipelineAction {
    override def implementPipeline(pipeline: Pipeline) = {
      println("pipeline: "+code)
      pipeline.changePipeline(code)
      true
    }
  }
  
  case class StepPipeline() extends PipelineAction {
    override def implementPipeline(pipeline: Pipeline) = {
      pipeline.stepPipeline()
      true
    }
  }
  
  case class RunPipeline() extends PipelineAction {
    override def implementPipeline(pipeline: Pipeline) = {
      pipeline.runPipeline()
      true
    }
  }
  
  case class ResetPipeline() extends PipelineAction {
    override def implementPipeline(pipeline: Pipeline) = {
      pipeline.resetPipeline()
      true
    }
  }
  
}