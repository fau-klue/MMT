    package info.kwarc.mmt.jedit

import info.kwarc.mmt.api._
import info.kwarc.mmt.api.frontend._
import info.kwarc.mmt.api.utils.File._
import org.gjt.sp.jedit._
import org.gjt.sp.jedit.msg._
import org.gjt.sp.jedit.textarea._
import javax.swing.SwingUtilities

/**
 * The main class of the MMTPlugin
 * after initialization, it creates a Controller and executes home/startup.mmt
 * logging information is sent to home/mmtplugin.log
 * the home directory is obtained from jEdit, e.g., settings/plugins/info.kwarc.mmt.jedit.MMTPlugin
 */
class MMTPlugin extends EBPlugin with Logger {
   val controller = new Controller
   val report = controller.report
   val logPrefix = "jedit"
   val errorSource = new MMTErrorSource

   val buildActions = new BuildActions(this)

   /** implements onNavigate hook in terms of the methods of MMTHyperlink */
   val mmtListener = new ChangeListener {
      override def onNavigate(p: Path) {
         log("navigating to " + p)
         val ref = controller.getO(p) flatMap {
            e => MMTHyperlink.elemToSourceRef(controller, e)
         }
         ref foreach {r =>
            val view = jEdit.getActiveView
            MMTHyperlink.navigateTo(view, r)
         }
      }
   }

   /** called by jEdit when plugin is loaded */
   override def start {
      val home = getPluginHome
      home.mkdirs
      controller.setHome(home)

      val startup = MMTOptions.startup.get.getOrElse("startup.msl")
      val file = home resolve startup
      if (file.exists)
         controller.execFileAction(file, None)
      
      val conf = MMTOptions.config.get.getOrElse("mmtrc")
      val confFile = home resolve conf
      if (confFile.exists)
         controller.loadConfig(MMTConfig.parse(confFile), false)

      errorlist.ErrorSource.registerErrorSource(errorSource)
      val archives = MMTOptions.archives.get orElse
        controller.getOAF.map(_.root.toString) getOrElse "mars"
      controller.addArchive(home resolve archives)
      // status bar is not actually available yet at this point
      controller.report.addHandler(StatusBarLogger)
      controller.extman.addExtension(mmtListener)
      jEdit.getViews foreach customizeView
      // make tooltips stay longer
      javax.swing.ToolTipManager.sharedInstance().setDismissDelay(100000)
   }
   /** called by jEdit when plugin is unloaded */
   override def stop {
      controller.cleanup
      errorlist.ErrorSource.unregisterErrorSource(errorSource)
      jEdit.getViews foreach clearMMTToolBar
   }

   override def handleMessage(message: EBMessage) {
     message match {
        //add MMTTextAreaExtension to every newly-created TextArea
        case epu: EditPaneUpdate =>
           epu.getWhat match {
             case EditPaneUpdate.CREATED =>
                log("handling " + epu.paramString)
                val editPane = epu.getSource.asInstanceOf[EditPane]
                customizeEditPane(editPane)
             case _ =>
            }
        case vup: ViewUpdate =>
           val view = vup.getView
           vup.getWhat match {
              case ViewUpdate.CREATED =>
                 log("handling " + vup.paramString)
                 customizeView(view)
              case ViewUpdate.CLOSED =>
                 log("handling " + vup.paramString)
                 clearMMTToolBar(view)
              case _ =>
           }
        case _ =>
      }
   }

  /** helper function that creates a thread and executes it */
  def invokeLater(code: => Unit) {
     SwingUtilities.invokeLater(
        new Runnable() {
          def run() {
            code
          }
        }
     )
  }
  
  private def customizeView(view: View) {
     view.getEditPanes foreach customizeEditPane
     addMMTToolBar(view)
  }
  private def customizeEditPane(editPane: EditPane) {
    val ta = editPane.getTextArea
    val painter = ta.getPainter
    if (!painter.getExtensions.exists(_.isInstanceOf[MMTTextAreaExtension])) {
      val taExt = new MMTTextAreaExtension(controller, editPane)
      painter.addExtension(TextAreaPainter.TEXT_LAYER, taExt)
    }
    //val sc = new StyleChanger(editPane, "mmt")
    //painter.addExtension(TextAreaPainter.DEFAULT_LAYER, sc)
    val ma = new MMTMouseAdapter(editPane)
    painter.addMouseListener(ma)

    /* old code used for cleaning up - seems unnecessary
      painter.putClientProperty(taKey, taExt)
       case EditPaneUpdate.DESTROYED =>
           log("handling " + epu.paramString)
           val taExt = painter.getClientProperty(taKey).asInstanceOf[TextAreaExtension]
           if (taExt != null) {
              painter.removeExtension(taExt)
              painter.putClientProperty(taKey, null)
           }*/
   }

  /** adds MMT toolbar */
  def addMMTToolBar(view: View) {
    invokeLater {
      clearMMTToolBar(view)
      val viewToolBar = view.getToolBar
      if (viewToolBar != null) {
        log("adding toolbar...")
        val newbar = new MMTToolBar(this)
        viewToolBar.add(newbar)
      }
    }
  }
  /** removes MMT toolbar */
  def clearMMTToolBar(view: View) {
    val viewToolBar = view.getToolBar
    if (viewToolBar != null) {
      log("Number of components of this view: " + viewToolBar.getComponentCount.toString)
      viewToolBar.getComponents foreach {comp => 
        if(comp.isInstanceOf[MMTToolBar]) {
          log("removing tool bar")
          viewToolBar.remove(comp)
        }
      }
    }
  }
}

object MMTPlugin {
   def isIDChar(c: Char) = (! Character.isWhitespace(c)) && "()[]{}:.".forall(_ != c)
   /** finds the id at a certain offset in a buffer
    * @param buffer a buffer
    * @param index offset in the buffer
    * @return the id at the offset, if any, as (line,beginOffsetInBuffer,endOffsetInBuffer,id)
    */
   def getCurrentID(buffer: Buffer, index: Int) : Option[(Int,Int,Int,String)] = {
      val line = buffer.getLineOfOffset(index)
      val lineStart = buffer.getLineStartOffset(line)
      val lineLength = buffer.getLineLength(line)
      if (lineLength == 0)
         return None
      var offset = index - lineStart
      val lineText = buffer.getLineText(line)
      if (offset == lineLength)
         offset = offset - 1
      if (! isIDChar(lineText(offset)))
         return None
      var left = offset // first character of id
      while (left > 0 && isIDChar(lineText(left - 1))) {left = left - 1}
      var right = offset // last character of id
      while (right < lineLength - 1 && isIDChar(lineText(right + 1))) {right = right + 1}
      Some((line, lineStart + left, lineStart + right + 1, lineText.substring(left, right + 1)))
   }
}

object StatusBarLogger extends ReportHandler("jEdit") {
  def apply(ind: Int, caller: => String, group: String, msg: List[String]) {
     val v = jEdit.getActiveView
     if (v != null) {
        v.getStatus.setMessage("MMT " + group + ": " + msg.headOption.getOrElse(""))
     }
  }
}
