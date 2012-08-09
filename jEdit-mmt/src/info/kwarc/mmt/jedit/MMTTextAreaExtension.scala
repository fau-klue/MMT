package info.kwarc.mmt.jedit

import info.kwarc.mmt.api._
import frontend._

import org.gjt.sp.jedit._
import textarea._
import syntax._
import java.awt.font.TextAttribute

/** A TextAreaExtension that is added to every EditPane
 *  it can be used for custom painting, e.g., background highlighting, tooltips
 *  Currently it does nothing
 */
class MMTTextAreaExtension(controller: Controller, editPane: EditPane) extends TextAreaExtension {
   private def log(msg: String) {controller.report("jedit-painter", msg)}
   private val textArea = editPane.getTextArea
   private val painter = textArea.getPainter
   override def paintValidLine(gfx: java.awt.Graphics2D, screenLine: Int, physicalLine: Int, startOffset: Int, endOffset: Int, y: Int) {
     //gfx.setColor(java.awt.Color.RED)
     //val height = painter.getLineHeight()
     //val startPoint = textArea.offsetToXY(startOffset)
     //val endPoint = textArea.offsetToXY(endOffset)
     //gfx.fillRect(0, y, 500, height)
   }
   //def getToolTipText(xCoord: Int, yCoord: Int) {} 
}

//to highlight the current expression implement this
//class MMTMatcher extends org.gjt.sp.jedit.textarea.StructureMatcher
//call editPane.getTextArea().addStructureMatcher, e.g., in sidekick parser's activate method, to register it

object StyleChanger {
   def hidden(style: SyntaxStyle) = {
      val newFont = style.getFont.deriveFont(0f)
      new SyntaxStyle(style.getForegroundColor, style.getBackgroundColor, newFont) 
   }
   def subscript(style: SyntaxStyle) = {
      val attributes = new java.util.Hashtable[TextAttribute,Int]
      attributes.put(TextAttribute.SUPERSCRIPT, TextAttribute.SUPERSCRIPT_SUB)
      val newFont = style.getFont.deriveFont(attributes)
      new SyntaxStyle(style.getForegroundColor, style.getBackgroundColor, newFont) 
   }
}

/** A TextAreaExtension that is added to a layer below TEXT_LAYER in order to change the painter's styles for a certain mode
 *  The painter's styles are set by the EditPane according to SyntaxUtilities.loadStyles.
 *  This class will override that setting.
 *  Tokens with type COMMENT4 will be hidden, regardless of its style settings. 
 */
class StyleChanger(editPane: EditPane, modeName: String) extends TextAreaExtension {
   private val textArea = editPane.getTextArea
   private val painter = textArea.getPainter
   override def paintValidLine(gfx: java.awt.Graphics2D, screenLine: Int, physicalLine: Int, startOffset: Int, endOffset: Int, y: Int) {
       if (editPane.getBuffer.getMode.getName == modeName) {
          val styles = painter.getStyles
          styles(Token.COMMENT4) = StyleChanger.hidden(styles(Token.COMMENT4))
          styles(Token.COMMENT3) = StyleChanger.subscript(styles(Token.COMMENT3))
       }
   }
}