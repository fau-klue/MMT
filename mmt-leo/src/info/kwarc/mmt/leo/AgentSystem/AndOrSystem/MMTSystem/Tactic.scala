package info.kwarc.mmt.leo.AgentSystem.AndOrSystem.MMTSystem

import info.kwarc.mmt.api._
import objects._

/**
 * A rule used for forward or backward proof search
 */
trait Tactic extends Rule {
   /**
    * convenience function to create an ApplicableTactic
    * 
    * to be used as in
    * 
    * {{{
    * def apply(...) = {
    *    // code for checking applicability 
    *    onApply {
    *       // code to run when applying the rule
    *    }
    * }
    * }}}
    */
   protected def onApply(l: => String)(cont: => LFProofTree) = {
      val at = new ApplicableTactic {
         def apply() = Some(cont)
         def label = l
      }
      Some(at)
   }
}

/**
 * invertible tactics can be applied greedily without leading a proof into a dead end
 * 
 * this type includes both invertible forward (e.g., existential elimination) and backwards rules (e.g., universal introduction) 
 */
trait InvertibleTactic extends Tactic {
   /**
    *  applies the tactic to a goal
    *  
    *  @param blackboard the registered blackboard, used for callbacks
    *  @param g the goal
    *  @return a continuation that returns the new goal(s)
    */
   def apply(blackboard: LFBlackboard, g: LFProofTree): Option[ApplicableTactic]
}

/**
 * an InvertibleTactic, whose behavior depends only on the conclusion of a goal
 */
trait BackwardInvertible extends InvertibleTactic {
   def apply(blackboard: LFBlackboard, g: LFProofTree): Option[ApplicableTactic]
}

/**
 * an InvertibleTactic, whose behavior depends only on the context of a goal
 */
trait ForwardInvertible extends InvertibleTactic {
   def apply(blackboard: LFBlackboard, context: Context): Option[ApplicableTactic]
   def apply(blackboard: LFBlackboard, g: LFProofTree): Option[ApplicableTactic] = apply(blackboard, g.context)
}

/**
 * a backward tactic generates additional ways to reach the goal
 * 
 * This is used in backward proof search 
 */
trait BackwardSearch extends Tactic {
   /**
    * backward rules change the goal so that usually only one rule can be applied if multiple are applicable
    * 
    * higher-prioritiy is used to decide which rule to apply  
    */ 
   def priority: Int

   /** applies the tactic to a goal
    *  
    *  @param blackboard the registered, used for callbacks
    *  @param g the goal
    *  @return a list of continuations each of which might solve the goal 
    */
   def apply(blackboard: LFBlackboard, g: LFProofTree): List[ApplicableTactic]
}

/**
 * a forward tactic generates additional facts that are implied by the assumptions
 * 
 * This is used in forward proof search
 */
trait ForwardSearch extends Tactic {
   /**
    * enriches a database of facts by one iteration
    */
   def generate(blackboard: LFBlackboard, interactive: Boolean): Unit
}

/**
 * a continuation function returned by a [[Tactic]] to be run if the tactic is to be applied
 * 
 * A tactic may return multiple continuations if it is applicable in multiple different ways.
 * Low-priority tactics may move expensive computations into the continuation to avoid unnecessary work
 */
abstract class ApplicableTactic {
   def label : String
   /** runs the continuation
    *  @return the new goals, None if application was not possible
    */
   def apply() : Option[LFProofTree]
}

object ApplicableTactic {
   def apply(a: LFProofTree, l: String) = new ApplicableTactic {
      def apply() = Some(a)
      val label = l
   }
}
