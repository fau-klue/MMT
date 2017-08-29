import info.kwarc.mmt.guidedtours.{Example, ExampleTopicMap, UserKarmaTemp}

object Mytest extends XeniaTest("debug"){
  def bar = 7
  def run: Unit = {

    println("Exaple aufrufen")
    val ex = new UserKarmaTemp("Ab")

    ex.wait()
  }


}
