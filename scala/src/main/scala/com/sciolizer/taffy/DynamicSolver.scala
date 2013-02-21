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

  def getChildVariables(variable: Variable[Values, Value]): List[Variable[Values, Value]] = {
    throw new NotImplementedError()
  }

  /* Instantiation contexts */

  abstract class InstantiationContext {
    def newVariable(sideEffectfulValues: Values, sideEffects: Value => Unit = DynamicSolver.noSideEffects[Value]): Variable[Values, Value]
    def newConstraint(constraint: Constraint)
  }

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

trait ContextContainer[Value] {
  def conditionedOn(assignments: List[VariableHasValue[Value]])(action: => Unit)
}

// todo: consider replacing with the Reject class. Or consider replacing the other one with this one.
case class VariableHasValue[Value](vid: Int, value: Value)

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
