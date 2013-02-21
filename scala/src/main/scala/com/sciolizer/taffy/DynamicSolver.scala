package com.sciolizer.taffy

import collection.mutable
import collection.mutable.ArrayBuffer
import scala.collection

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/15/13
 * Time: 11:32 AM
 */
class DynamicSolver[Constraint, Values, Value](domain: Domain[Constraint, Values, Value], ranger: Ranger[Values, Value], candidateValues: Values) {

  private var instantiationContext: InstantiationContext = new SideEffectContext(List.empty)
  private val variables: ArrayBuffer[Variable[Values, Value]] = ArrayBuffer()
  private val constraints: mutable.Set[ConstraintWrapper] = mutable.Set.empty

  // Most of the time creates a new variable.
  // But if called from within a side effect, it might return an already existing variable.
  def newVariable(sideEffectfulValues: Values, sideEffects: Value => Unit = DynamicSolver.noSideEffects[Value]): Variable[Values, Value] =
    instantiationContext.newVariable(sideEffectfulValues, sideEffects)

  def newConstraint(constraint: Constraint) { instantiationContext.newConstraint(constraint) }

  def solve(isomorphisms: Isomorphisms = NoIsomorphisms): Option[Map[Variable[Values, Value], Value]] = {
    do {
      val numVariables = variables.size
      val p = new Problem[ConstraintWrapper, Values, Value](numVariables, Set.empty ++ constraints, candidateValues, isomorphisms)
      val listener = new AssignmentListener[Value] {
        def assignment(vid: Int, value: Value) {
          variables(vid).succcessfulAssignment(value)
        }
      }
      val sss = new SuperSimpleSolver[ConstraintWrapper, Values, Value](new DomainWrapper, p, ranger)
      sss.backtrackingSearch((0 until numVariables).map(x => x -> candidateValues).toMap, listener) match {
        case None => throw new NotImplementedError() // need to run side effects
        case Some(solution) =>
          return Some(solution.map(x => (variables(x._1), x._2)))
      }
    } while (nextLevel())
  }

  // returns true iff an expansion was made
  private def nextLevel(): Boolean = {
    val contextContainer: ContextContainer[Value] = new ContextContainer[Value] {
      def conditionedOn(assignments: List[VariableHasValue[Value]])(action: => Unit) {
        for (vv <- assignments) {
          constraints -= Reject(vv.vid, vv.value)
        }
        val originalContext = instantiationContext
        try {
          instantiationContext = new SideEffectContext(assignments)
          action
        } finally {
          instantiationContext = originalContext
        }
      }
    }
    variables.exists(_.expand(contextContainer))
  }

  // Since the client code makes the list of side effectful values explicit, we don't actually
  // need to probe for them.
//  private def analyzeSideEffects(sideEffectfulValues: Values, sideEffects: Value => Unit): Set[Value] = {
//    val ret: mutable.Set[Value] = mutable.Set.empty
//    var vid = 0
//    val vars: mutable.Set[Variable[Values, Value]] = mutable.Set.empty
//    val constraints: mutable.Set[Constraint] = mutable.Set.empty
//    val ic = new InstantiationContext {
//
//      def newVariable(sideEffectfulValues: Values, sideEffects: (Value) => Unit): Variable[Values, Value] = {
//        val ret = new Variable[Values, Value](vid, sideEffectfulValues, sideEffects, List.empty)
//        vars += ret
//        vid += 1
//        ret
//      }
//
//      def newConstraint(constraint: Constraint) {
//        constraints += constraint
//      }
//    }
//
//    for (value <- ranger.iterate(sideEffectfulValues)) {
//      vars.clear()
//      constraints.clear()
//      withInstantiationContext(ic) {
//        sideEffects(value)
//      }
//      if (!vars.isEmpty) {
//        ret += value
//      }
//    }
//    Set.empty ++ ret
//  }

  def getChildVariables(variable: Variable[Values, Value]): List[Variable[Values, Value]] = {
    throw new NotImplementedError()
  }


  /* Instantiation contexts */

  abstract class InstantiationContext {
    def newVariable(sideEffectfulValues: Values, sideEffects: Value => Unit = DynamicSolver.noSideEffects[Value]): Variable[Values, Value]
    def newConstraint(constraint: Constraint)
  }
                           // Actually this just looks like SideEffectContext where assignments is the empty string
//  class RootContext extends InstantiationContext {
//    def newVariable(sideEffectfulValues: Values, sideEffects: Value => Unit = DynamicSolver.noSideEffects[Value]): Variable[Values, Value] = {
//      val ret = new Variable(variables.size, sideEffectfulValues, sideEffects)
//      variables.append(ret)
//      ret
//    }
//
//    def newConstraint(constraint: Constraint) {
//      constraints += Vanilla(constraint)
//    }
//  }

  class SideEffectContext(assignments: List[VariableHasValue[Value]]) extends InstantiationContext {

    def newVariable(sideEffectfulValues: Values, sideEffects: (Value) => Unit): Variable[Values, Value] = {
      val ret = new Variable(variables.size, sideEffectfulValues, sideEffects, assignments)
      for (value <- sideEffectfulValues) {
        constraints += Reject(ret.varId, value)
      }
      variables.append(ret)
      ret
    }

    def newConstraint(constraint: Constraint) {
      constraints += ConditionalConstraint(constraint, assignments)
    }

  }

  /* Constraint wrappers */

  class DomainWrapper extends Domain[ConstraintWrapper, Values, Value] {
    def revise(rw: ReadWrite[Values, Value], c: ConstraintWrapper): Boolean = c.revise(rw)
    def coverage(c: ConstraintWrapper): collection.Set[VarId] = c.coverage
    def substitute(c: ConstraintWrapper, substitution: Map[VarId, VarId]): ConstraintWrapper = c.substitute(substitution)
  }

  abstract class ConstraintWrapper {
    def revise(rw: ReadWrite[Values, Value]): Boolean
    val coverage: Set[Int]
    def substitute(substitution: Map[Int, Int]): ConstraintWrapper
  }

  case class ConditionalConstraint(inner: Constraint, assignments: List[VariableHasValue[Value]]) extends ConstraintWrapper {
    def revise(rw: ReadWrite[Values, Value]): Boolean = {
      for (assignment <- assignments) {
        if (!ranger.equals(rw.readVar(assignment.vid), ranger.toSingleton(assignment.value))) {
          return true
        }
      }
      domain.revise(rw, inner)
    }
    lazy val coverage = domain.coverage(inner) ++ assignments.map(_.vid)
    def substitute(substitution: Map[Int, Int]): ConstraintWrapper =
      ConditionalConstraint(domain.substitute(inner, substitution), assignments.map(x => x.copy[Value](vid = substitution(x.vid))))
  }

  case class Reject(vid: Int, value: Value) extends ConstraintWrapper {
    def revise(rw: ReadWrite[Values, Value]): Boolean = {
      rw.shrinkVar(vid, value)
      true
    }
    lazy val coverage = Set(vid)
    def substitute(substitution: Map[Int, Int]): ConstraintWrapper = copy(vid = substitution(vid))
  }

  case class Vanilla(inner: Constraint) extends ConstraintWrapper {
    def revise(rw: ReadWrite[Values, Value]): Boolean = domain.revise(rw, inner)
    lazy val coverage: Set[Int] = domain.coverage(inner).asInstanceOf[Set[Int]]
    def substitute(substitution: Map[Int, Int]): ConstraintWrapper = Vanilla(domain.substitute(inner, substitution))
  }
}

object DynamicSolver {
  def noSideEffects[Value](value: Value) { }
}

// order of the variables is important
case class Expansion[Constraint, Value](variables: List[Variable[Constraint, Value]], constraints: List[Constraint])

trait ContextContainer[Value] {
  def conditionedOn(assignments: List[VariableHasValue[Value]])(action: => Unit)
}

// todo: consider replacing with the Reject class. Or consider replacing the other one with this one.
case class VariableHasValue[Value](vid: Int, value: Value)

trait VariableCreator[Constraint, Value] {
  def makeVariable(): Variable[Constraint, Value]
}

class Variable[Values, Value](val varId: Int, val sideEffectfulValues: Values, effects: Value => Unit, ancestors: List[VariableHasValue[Value]]) {
  private val successfulAssignments: mutable.Set[Value] = mutable.Set.empty
  // todo: add a check to make sure that Value has a legitimate equals() and hashCode()
  private val expanded: mutable.Set[Value] = mutable.Set.empty
  def succcessfulAssignment(value: Value) {
    successfulAssignments += value
  }
  def expand(contextContainer: ContextContainer[Value]): Boolean = {
    var ret = false
    for (value <- successfulAssignments) {
      if (!expanded.contains(value)) {
        ret = true
        contextContainer.conditionedOn(VariableHasValue(varId, value) +: ancestors) {
          effects(value)
        }
        expanded += value
      }
    }
    ret
  }

  // todo: add side effect memoization
  override def equals(obj: Any): Boolean = varId == obj.asInstanceOf[Variable[Values, Value]].varId
  override def hashCode(): Int = varId.hashCode()
}

//trait ConstraintInstantiator[Constraint] {
//  def newConstraint(constraint: Constraint)
//}
//trait Instantiator[Constraint, Value] extends ConstraintInstantiator[Constraint] {
//  def newVariable(sideEffects: SideEffects[Constraint, Value] = noSideEffects): Variable[Value]
//  lazy val noSideEffects: SideEffects[Constraint, Value] = new SideEffects[Constraint, Value] {
//    def run(variable: Variable[Value], value: Value, instantiator: Instantiator[Constraint, Value]) { }
//  }
//}

//trait Init[Constraint, Value] extends Instantiator[Constraint, Value] {
//  def newTemplate[A](template: Instantiator[Constraint, Value] => A): Template[Constraint, Value, A]
//}

//trait Template[Constraint, Value, A] {
//  def instantiate(inst: Instantiator[Constraint, Value]): A
//}
                     /*
trait SideEffects[Constraint, Value] {
  def forValue(variable: Variable[Value], value: Value): SideEffect[Constraint, Value]
}

trait SideEffect[Constraint, Value] {
  val numVariables: Int
  def constraints(vars: List[Variable[Value]], instantiator: ConstraintInstantiator[Constraint])
}*/