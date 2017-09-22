package info.kwarc.mmt.lf
import info.kwarc.mmt.api._
import objects._
import checking._
import objects.Conversions._
import uom._
import utils.MyList.fromList

object Common {
   /** checks that a type can be quantified over
    *  to maximize extensibility, we allow a bound variables x:a if a:U:kind for some U
    *
    *  in plain LF, this is only possible if U=type, i.e., if a:type
    *  other frameworks may want to reuse the LF typing rules with more options for U
    */
   def isTypeLike(solver: Solver, a: Term)(implicit stack: Stack, history: History) = {
     val h = history + "checking the size of the type of the bound variable"
     val kind = OMS(Typed.kind)
     val tp = OMS(Typed.ktype)
     solver.inferTypeAndThen(a)(stack, h) {aT =>
        if (aT == kind) {
          solver.error("type of bound variable is too big: " + solver.presentObj(aT))
        } else {
          val iskind = solver.dryRun(false,true)(solver.check(Typing(stack, aT, kind, Some(OfType.path)))(h))
          if (iskind.get contains true) true else solver.check(Subtyping(stack,aT,tp))
        }
     }
   }

   /** performs safe simplifications and variable transformation to force the argument to become a Pi
    * @param solver the Solver
    * @param tp the function type
    * @return a type equal to tp that may have Pi shape  
    */
   def makePi(solver: Solver, tp: Term)(implicit stack: Stack, history: History): Term = {
      val tpS = solver.safeSimplifyUntil(tp)(Pi.unapply)._1
      tpS match {
         case Pi(x,a,b) => tpS
         case ApplyGeneral(OMV(m), args) =>
           // check that tp is unknown applied to variables 
           if (! solver.getUnsolvedVariables.isDeclared(m)) {
              return tpS
           }
           args foreach {
              case OMV(u) => 
              case _ => return tpS
           }
           val mD = OMV(m/"d")
           val mC = OMV(m/"c")
           val mV = OMV(m/"v")
           val mSol = Pi(mV.name, ApplyGeneral(mD, args), ApplyGeneral(mC, args ::: List(mV)))
           // if we have not done the variable transformation before, add the new unknowns
           if (! solver.getPartialSolution.isDeclared(mD.name)) {
              val newVars = Context(VarDecl(mD.name), VarDecl(mC.name))
              solver.addUnknowns(newVars, Some(m))
           }
           history += ("trying to solve "+m+" as "+solver.presentObj(mSol))
           // solve m in terms of newVars
           val success = solver.check(Equality(stack, tpS, mSol, Some(OMS(Typed.ktype)))) //TODO does this work for polymorphism?
           if (success) mSol else tpS
         case _ => tpS 
      }
   }
   def pickFresh(solver: Solver, x: LocalName)(implicit stack: Stack) =
      Context.pickFresh(solver.constantContext ++ solver.getPartialSolution ++ stack.context, x)
   
   /** true if a term is an unknown applied to arguments */
   def isUnknownTerm(solver: Solver, t: Term) = t match {
     case ApplyGeneral(OMV(u), _) => solver.getUnsolvedVariables.isDeclared(u)
     case _ => false
   }
}

import Common._

trait PiOrArrowRule {self: CheckingRule =>
  override def alternativeHeads = List(Arrow.path)
}

/** Formation: the type inference rule x:A:type|-B:U  --->  Pi x:A.B : U
 * This rule works for any universe U
  * */
object PiTerm extends FormationRule(Pi.path, OfType.path) with PiOrArrowRule {
   def apply(solver: Solver)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History) : Option[Term] = {
      tm match {
        case Pi(x,a,b) =>
           isTypeLike(solver,a)
           val (xn,sub) = Common.pickFresh(solver, x)
           solver.inferType(b ^? sub)(stack ++ xn % a, history) flatMap {bT =>
              if (bT.freeVars contains xn) {
                 // usually an error, but xn may disappear later, especially when unknown in b are not solved yet 
                 //solver.error("type of Pi-scope has been inferred, but contains free variable " + xn + ": " + solver.presentObj(bT))
                 None
              } else
                 Some(bT)
           }
        case _ => None // should be impossible
      }
   }
}

/** Introduction: the type inference rule x:A|-t:B  --->  lambda x:A.t : Pi x:A.B
 * This rule works for B:U for any universe U
  * */
object LambdaTerm extends IntroductionRule(Lambda.path, OfType.path) {
   def apply(solver: Solver)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History) : Option[Term] = {
      tm match {
        case Lambda(x,a,t) =>
           if (!covered) solver.inferType(a)//isTypeLike(solver,a)
           val (xn,sub) = Common.pickFresh(solver, x)
           solver.inferType(t ^? sub)(stack ++ xn % a, history) map {b => Pi(xn,a,b)}
        case _ => None // should be impossible
      }
   }
}

/** common code for rules regarding the elimination-form: inference and reduction */
abstract class ArgumentChecker {  
   /** checks if argument tm can be supplied for expected type tp */
   def apply(solver: CheckingCallback)(tm: Term, tp: Term, covered: Boolean)(implicit stack: Stack, history: History): Boolean
}

/** default implementation: type-check against expected type if not covered; skip if covered */
object StandardArgumentChecker extends ArgumentChecker {
   def apply(solver: CheckingCallback)(tm: Term, tp: Term, covered: Boolean)(implicit stack: Stack, history: History) = {
     history.indented {
      covered || solver.check(Typing(stack, tm, tp))
     }
   }
}


/** Elimination: the type inference rule f : Pi x:A.B  ,  conforms(t,A)  --->  f t : B [x/t]
 *
 * This rule works for B:U for any universe U
 * 
 * This rule implements currying and all arguments at once 
 */
class GenericApplyTerm(conforms: ArgumentChecker) extends EliminationRule(Apply.path, OfType.path) {
   def apply(solver: Solver)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History) : Option[Term] = {
      // calling Beta first could make this rule more reusable because it would avoid inferring the type of a possibly large lambda 
      
      // auxiliary function that handles one argument at a time
      def iterate(fT: Term, args: List[Term]): Option[Term] = {
         (fT,args) match {
           case (_, Nil) =>
             history += "no arguments, type is: " + solver.presentObj(fT)
             Some(fT)
           case (Pi(x,a,b), t::rest) =>
              history += "function type is: " + solver.presentObj(fT)
              history += "argument is: " + solver.presentObj(t)
              val check = conforms(solver)(t, a, covered)(stack, history + "checking argument")
              if (check) { 
                 history += "substituting argument in return type"
                 // substitute for x and newly-solved unknowns (as solved by conforms) and simplify
                 val bS = solver.substituteSolved(b ^? (x/t), true)
                 iterate(bS, rest)
              } else {
                history += "argument check did not succeed: " + solver.presentObj(t) + ":" + solver.presentObj(a) + ", giving up for now"
                None
              }
           /*case ApplyGeneral(OMV(u), _) =>
              history += "does not look like a function type at this point"
              None*/
           case _ =>
              val fTPi = Common.makePi(solver, fT)
              if (fTPi != fT)
                 iterate(fTPi, args)
              else {
                val unks = solver.getUnsolvedVariables
                if (fTPi.freeVars.exists(unks.isDeclared)) {
                   // this might be convertible into a function type once the unknown variable is solved
                   history += "does not look like a function type at this point"
                   solver.error("this is not a function type (type level rewriting is not supported)")
                   None
                } else {
                   None
                }
              }
        }
      }
      tm match {
         case ApplySpine(f,args) =>
            history += "inferring type of function " + solver.presentObj(f)
            val fTOpt = solver.inferType(f, covered)(stack, history.branch)
            fTOpt match {
              case Some(fT) =>
                iterate(fT, args)
              case None =>
                history += "failed"
                //TODO commented out because it looks redundant, check if it's ever helpful
                //args.foreach {t => solver.inferType(t)(stack, history.branch)} // inference of the argument may solve some variables
                None
            }
         case _ =>
            None // should be impossible
      }
   }
}

/** the usual inference rule with conforms(t,A) = t:A */
object ApplyTerm extends GenericApplyTerm(StandardArgumentChecker)

/** type-checking: the type checking rule x:A|-f x:B  --->  f : Pi x:A.B */
// TODO all typing rules of this style are in danger of accepting an expression if all eliminations are well-formed but the term itself is not
//  e.g., [x:Int]sqrt(x) : Nat->Real  would check
object PiType extends TypingRule(Pi.path) with PiOrArrowRule {
   def apply(solver: Solver)(tm: Term, tp: Term)(implicit stack: Stack, history: History) : Boolean = {
      (tm,tp) match {
         case (Lambda(x1,a1,t),Pi(x2,a2,b)) =>
            // this case is somewhat redundant, but allows reusing the variable name
            solver.check(Equality(stack,a1,a2,None))(history+"domains must be equal")
            val (xn,sub1) = Common.pickFresh(solver, x1)
            val sub2 = x2 / OMV(xn)
            val nt = solver.substituteSolved(a2,true)
           // seems to be necessary, in case a2 has only been solved during the equality check above...
            solver.check(Typing(stack ++ xn % nt, t ^? sub1, b ^? sub2))(history + "type checking rule for Pi")
         case (tm, Pi(x2, a2, b)) =>
            val (xn,sub) = Common.pickFresh(solver, x2)
            val j = Typing(stack ++ xn % a2,  Apply(tm, xn), b ^? sub)
            solver.check(j)(history + "type checking rule for Pi")
      }
   }
}

/** equality-checking: the extensionality rule (equivalent to Eta) x:A|-f x = g x : B --->  f = g  : Pi x:A. B
 * If possible, the name of the new variable x is taken from f, g, or their type; otherwise, a fresh variable is invented. */
object Extensionality extends TypeBasedEqualityRule(Nil, Pi.path) with PiOrArrowRule {
   def apply(solver: Solver)(tm1: Term, tm2: Term, tp: Term)(implicit stack: Stack, history: History): Option[Boolean] = {
      val Pi(x, a, b) = tp
      // pick fresh variable name, trying to reuse existing name 
      val xBase = (tm1, tm2) match {
         case (Lambda(x1, _, _), Lambda(x2,_,_)) if x1 == x2 => x1
         case _ => x
      }
      val (xn,_) = Context.pickFresh(stack.context, xBase)
      val tm1Eval = Apply(tm1, OMV(xn))
      val tm2Eval = Apply(tm2, OMV(xn))
      val bsub = b ^? (x / OMV(xn))
      Some(solver.check(Equality(stack ++ xn % a, tm1Eval, tm2Eval, Some(bsub))))
   }
}

/** Congruence for Lambda
 *  
 *  We cannot use CongruenceRule here because we have to flatten nested lambdas in addition.
 *  
 *  This rule is a special case of Extensionality, but it does not make use of the type.
 */
object LambdaCongruence extends TermHeadBasedEqualityRule(Nil, Lambda.path, Lambda.path) {
   def apply(checker: CheckingCallback)(tm1: Term, tm2: Term, tp: Option[Term])(implicit stack: Stack, history: History) = {
      (tm1,tm2) match {
         case (Lambda(x1,a1,t1), Lambda(x2,a2,t2)) =>
            val cont = Continue {
               history += "congruence for lambda"
               val res1 = checker.check(Equality(stack,a1,a2,None))(history + "equality of domain types")
               val (xn,_) = Context.pickFresh(stack.context, x1)
               val t1sub = t1 ^? (x1 / OMV(xn))
               val t2sub = t2 ^? (x2 / OMV(xn))
               val res2 = checker.check(Equality(stack ++ xn % a1, t1sub, t2sub, None))(history + "equality of scopes")
               res1 && res2
            }
            Some(cont)
         case _ => None
      }
   }
}

/** Congruence for Pi
 *  
 *  We cannot use HeadBasedEqualityRule here because we have to flatten nested Pis and consider -> in addition.
 */
object PiCongruence extends TermBasedEqualityRule with PiOrArrowRule {
   val head = Pi.path
   def applicable(tm1: Term, tm2: Term) = heads.contains(tm1.head.orNull) && heads.contains(tm2.head.orNull)
   def apply(checker: CheckingCallback)(tm1: Term, tm2: Term, tp: Option[Term])(implicit stack: Stack, history: History) = {
      (tm1,tm2) match {
         case (Pi(x1,a1,t1), Pi(x2,a2,t2)) =>
            val cont = Continue {
               history += "congruence for function types"
               val res1 = checker.check(Equality(stack,a1,a2,None))(history + "equality of domain types")
               val (xn,_) = Context.pickFresh(stack.context, x1)
               val t1sub = t1 ^? (x1 / OMV(xn))
               val t2sub = t2 ^? (x2 / OMV(xn))
               val res2 = checker.check(Equality(stack ++ xn % a1, t1sub, t2sub, None))(history + "equality of scopes")
               res1 && res2
            }
            Some(cont)
         case _ => None
      }
   }
}

/**
 * the beta-reduction rule reducible(s,A)  --->  (lambda x:A.t) s = t [x/s]
 * 
 * the reducibility judgment is left abstract, usually the typing judgment s:A
 * 
 * This rule also normalizes nested applications so that it implicitly implements the currying rule (f s) t = f(s,t).
 */
class GenericBeta(conforms: ArgumentChecker) extends ComputationRule(Apply.path) {
   
   def apply(solver: CheckingCallback)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History) : Option[Term] = {
      var reduced = false // remembers if there was a reduction
      // auxiliary recursive function to beta-reduce as often as possible
      // returns Some(reducedTerm) or None if no reduction
      def reduce(f: Term, args: List[Term]): Option[Term] = (f,args) match {
         case (Lambda(x,a,t), s :: rest) =>
            if (conforms(solver)(s,a,covered)) {
              reduced = true
              reduce(t ^? (x / s), rest)
            } else {
              history += "cannot beta-reduce at this point"
              None
            }
         case (f, Nil) =>
            //all arguments were used, recurse in case f is again a redex
            //otherwise, return f (only possible if there was a reduction, so no need for 'if (reduced)')
            apply(solver)(f, covered) orElse Some(f)
         case _ => 
            /*// simplify f recursively to see if it becomes a Lambda
            val fS = solver.simplify(f)
            if (f != fS) reduce(fS, args)
            else {*/
              //no more reduction possible
              if (reduced)
                Some(ApplySpine(f,args : _*))
              else
                None
      }
      tm match {
         //using ApplySpine here also normalizes curried application by merging them into a single one
         case ApplySpine(f, args) => reduce(f, args)
         case _ => None // only possible after recursing
      }
   }
}

/**
 * the usual beta-reduction rule s : A  --->  (lambda x:A.t) s = t [x/s]
 */ 
object Beta extends GenericBeta(StandardArgumentChecker)

/*
/**
 *  should be redundant, but maybe more efficient
 */
object UnsafeBeta extends BreadthRule(Apply.path){
   val apply = (args: List[Term]) => {
      // collects the substitution that will be applied (thus, we only substitute once even if there are multiple nested redexes) 
      var sub = Substitution()
      // repeatedly checks for a redex and returns the reduced terms
      def reduce(f: Term, args: List[Term]): Change = (f,args) match {
         case (Lambda(x,a,t), s :: rest) => 
            sub = sub ++ (x / s)
            reduce(t, rest)
         case (f, Nil) =>
            //all arguments were used (only possible if there was a reduction)
            GlobalChange(f ^? sub)
         case _ => 
            if (sub.isEmpty)
              NoChange
            else
              GlobalChange(ApplySpine(f ^? sub, args : _*))
      }
      reduce(args.head, args.tail)
   }
}
*/


/** A simplification rule that implements A -> B = Pi x:A.B  for fresh x.
 * LocalName.Anon is used for x */
// not used anymore because Pi rules now also apply to arrow
object ExpandArrow extends ComputationRule(Arrow.path) {
   def apply(solver: CheckingCallback)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History) : Option[Term] = tm match {
      case Arrow(a,b) => Some(Pi(OMV.anonymous, a, b))
      case _ => None
   }
}

class Injectivity(val head: GlobalName) extends TermBasedEqualityRule {
   def applicable(tm1: Term, tm2: Term) = (tm1,tm2) match {
      case (ApplySpine(OMS(this.head),args1),ApplySpine(OMS(this.head),args2)) => args1.length == args2.length
      case _ => false
   }
   def apply(check: CheckingCallback)(tm1: Term, tm2: Term, tp: Option[Term])(implicit stack: Stack, history: History) = {
      val (ApplySpine(_,args1),ApplySpine(_,args2)) = (tm1,tm2)
      //if check.getDef(head) == None && check.getTp(head) returns type
      None
   }
}

// experimental (requiring that torso is variable does not combine with other solution rules) 
object SolveMultiple extends SolutionRule(Apply.path) {
   def applicable(tm1: Term) = tm1 match {
      case ApplySpine(OMV(_),_) => Some(0)
      case _ => None
   }
   def apply(j: Equality): Option[(Equality,String)] = {
      j.tm1 match {
         case ApplySpine(OMV(u), args) =>
             // solver.unknowns.isDeclared(u) known by precondition
             // make sure tm1 is of the form u x1 ... xn
             val bvarArgs = args map {
                case OMV(x) => x
                case _ => return None
             }
             // split context into bind = x1, ..., xn and the rest
             val (bind, rest) = j.stack.context.variables.partition {case vd => bvarArgs contains vd.name}
             // this guarantees that all xi are declared in stack.context and are distinct 
             if (bind.distinct.length != bvarArgs.length) return None
             //TODO check that no variable declaration in rest depends on an xi
             //TODO use rest instead of stack
             val cont = Context(bind:_*)
             // check that Lambda(cont,tm2) is closed
             val tm2Closed = j.tm2.freeVars forall {x => cont.isDeclared(x)}
             if (! tm2Closed) return None
             Some((Equality(j.stack, OMV(u), Lambda(cont, j.tm2), None), "binding variables"))
         case _ => None
      }
   }
}

/** solution: This rule tries to solve for an unknown by applying lambda-abstraction on both sides and eta-reduction on the left.
 *  Its effect is, for example, that X x = t is reduced to X = lambda x.t where X is a meta- and x an object variable. 
 */
object Solve extends SolutionRule(Apply.path) {
   def applicable(t: Term) = t match {
      case Apply(_, _) => Some(0)  // do not match for OMV(_) here: unknowns in function position belong to this rule even if the rule can't do anything
      case _ => None
   }
   def apply(j: Equality): Option[(Equality, String)] = {
      j.tm1 match {
         case Apply(t, OMV(x)) =>
             val i = j.stack.context.lastIndexWhere(_.name == x)
             if (i == -1) return None
             var dropped = List(x) // the variables that we will remove from the context
             var newCon : Context = j.stack.context.take(i) // the resulting context
             // iterate over the variables vd after x
             j.stack.context.drop(i+1) foreach {vd =>
                if (vd.freeVars.exists(dropped.contains)) {
                   // vd depends on x, we use weakening to drop vd as well
                   dropped ::= vd.name
                } else {
                   // append vd to the new context
                   newCon = newCon ++ vd
                }
             }
             // check whether weakening is applicable: dropped variables may not occur in t or Lambda(x,a,tm2)
             if (t.freeVars.exists(dropped.contains))
                // most important special case: x occurs free in t so that eta is not applicable
                return None
             if (j.tm2.freeVars.exists(dropped.filterNot(_ == x) contains _))
                return None
             // get the type of x and abstract over it
             j.stack.context.variables(i).tp match {
                case Some(a) => 
                   val newStack = j.stack.copy(context = newCon)
                   Some((Equality(newStack, t, Lambda(x, a, j.tm2), j.tpOpt map {tp => Pi(x,a,tp)}), "binding x"))
                case _ => None
             }
         case _ => None
      }
   }
}

/** This rule tries to solve for an unkown by applying lambda-abstraction on both sides and eta-reduction on the left.
 *  Its effect is, for example, that X x = t is reduced to X = lambda x.t where X is a meta- and x an object variable. 
 */
object SolveType extends TypeSolutionRule(Apply.path) {
   def apply(solver: Solver)(tm: Term, tp: Term)(implicit stack: Stack, history: History): Boolean = {
      tm match {
         case Apply(t, OMV(x)) =>
             val i = stack.context.lastIndexWhere(_.name == x)
             if (i == -1) return false
             var dropped = List(x) // the variables that we will remove from the context
             var newCon : Context = stack.context.take(i) // the resulting context
             // iterate over the variables vd after x
             stack.context.drop(i+1) foreach {vd =>
                if (vd.freeVars.exists(dropped.contains _)) {
                   // vd depends on x, we use weakening to drop vd as well
                   dropped ::= vd.name
                } else {
                   // append vd to the new context
                   newCon = newCon ++ vd
                }
             }
             // check whether weakening is applicable: dropped variables may not occur in t or Lambda(x,a,tm2)
             if (t.freeVars.exists(dropped.contains _))
                // most important special case: x occurs free in t so that eta is not applicable
                return false
             if (tp.freeVars.exists(dropped.filterNot(_ == x) contains _))
                return false
             // get the type of x and abstract over it
             stack.context.variables(i).tp match {
                case Some(a) => 
                   val newStack = stack.copy(context = newCon)
                   solver.solveTyping(t, Pi(x, a, tp))(newStack, history + ("solving by binding " + x))
                case _ => false
             }
         case _ => false
      }
   }
}

object TheoryTypeWithLF extends ComputationRule(ModExp.theorytype) {
   def apply(solver: CheckingCallback)(tm: Term, covered: Boolean)(implicit stack: Stack, history: History) = tm match {
      case TheoryType(params) =>
         if (params.isEmpty) None else Some(Pi(params, TheoryType(Nil)))
      case _ => None
   }
}