package info.kwarc.mmt.guidedtours

import info.kwarc.mmt.api.{Path, ontology}
import info.kwarc.mmt.api.frontend.Controller
import info.kwarc.mmt.api.ontology.HasCodomain


class Example(controllerAttribute: Controller) {
  //val name : Path = theoryName
  val controller = controllerAttribute
  val topics : List[Path] = this.updateTopics()
  val avgDifficulty : Double = this.updateDifficulty()
  val avgTime : Double = this.updateAvgTime()
  
  // The rating does not appear here because it is relevant only to a single topic. 
  // "The quick brown fox jumps over a lazy dog" is a good example of a sentence that covers all letters of the alphabet,
  // it's useless otherwise
  
  private def updateTopics() : List[Path] = {
    val examples = controller.depstore.getInds(???)//.getSubjects(ontology.HasCodomain, flexiformal.FragPath(name))
    examples.toList
  }
  
  private def updateDifficulty() : Double = {
    val allTopics = topics.map{x => {
      //new ExampleTopicMap(name, x)
    }}
    
    //allTopics
    0.0
  }
  
  private def updateAvgTime() : Double = {
    0.0
  }
  
  def getRating(topic: Path) : Double = {
    0.0
  }
}