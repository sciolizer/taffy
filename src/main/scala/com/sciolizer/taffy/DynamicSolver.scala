package com.sciolizer.taffy

import collection.mutable
import collection.mutable.{ListBuffer, ArrayBuffer}
import scala.collection
import collection.immutable.ListMap
import com.sciolizer.taffy.Variable.Assignments

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/15/13
 * Time: 11:32 AM
 */
class DynamicSolver[Constraint <: Revisable[Values, Value], Values, Value](domain: Inference[Constraint], ranger: Ranger[Values, Value], candidateValues: Values) {
  type VarId = Int
  type Assignment = Tuple2[VarId, Value]

  private var instantiationContext: InstantiationContext = new InstantiationContext(List.empty)
  private val variables: ArrayBuffer[Variable[Value]] = ArrayBuffer()
  private val constraints: mutable.Set[ConstraintWrapper] = mutable.Set.empty
  private var solution: Option[Map[VarId, Value]] = None

  // Most of the time creates a new variable.
  // But if called from within a side effect, it might return an already existing variable.
  def newVariable(sideEffectfulValues: Set[Value], sideEffects: Value => Unit = DynamicSolver.noSideEffects[Value]): Variable[Value] =
    instantiationContext.newVariable(sideEffectfulValues, sideEffects)

  def newConstraint(constraint: Constraint) { instantiationContext.newConstraint(constraint) }

  def solve(isomorphisms: Isomorphisms = NoIsomorphisms): Boolean = {
    do {
      val numVariables = variables.size
      val p = new Problem[ConstraintWrapper, Values, Value](numVariables, Set.empty ++ constraints, candidateValues, isomorphisms)
      val listener = new AssignmentListener[Value] {
        def assignment(vid: Int, value: Value) {
          variables(vid).succcessfulAssignment(value)
        }
      }
      val sss = new SuperSimpleSolver[ConstraintWrapper, Values, Value](new InferenceWrapper, p, ranger)
      sss.backtrackingSearch((0 until numVariables).map(x => x -> candidateValues).toMap, listener) match {
        case Some(sol) =>
          solution = Some(sol) // .map(x => (variables(x._1), x._2)))
          return true
        case None =>
      }
    } while (nextLevel())
    false
  }

  // returns true iff an expansion was made
  private def nextLevel(): Boolean = {
    val contextContainer: Variable.ContextContainer[Value] = new Variable.ContextContainer[Value] {

      def conditionedOn(dependencies: List[(VarId, Value)])(action: => Unit): List[Variable[Value]] = {
        for (vv <- dependencies) {
          constraints -= Reject(vv._1, vv._2)
        }
        val originalContext = instantiationContext
        try {
          instantiationContext = new InstantiationContext(dependencies)
          action
          instantiationContext.created
        } finally {
          instantiationContext = originalContext
        }
      }

    }
    variables.exists(_.expand(contextContainer))
  }

  /* Instantiation contexts */


  lazy val assignments: Variable.Assignments[Value] = new Assignments[Value] {
    def value(vid: Variable.VarId): Value = solution match {
      case None => throw new IllegalStateException("No solution")
      case Some(sol) => sol(vid)
    }
  }

  class InstantiationContext(dependencies: List[Assignment]) {
    private[this] val _created: ListBuffer[Variable[Value]] = ListBuffer.empty

    def created: List[Variable[Value]] = _created.toList

    def newVariable(sideEffectfulValues: Set[Value], sideEffects: (Value) => Unit = DynamicSolver.noSideEffects[Value]): Variable[Value] = {
      val ret: Variable[Value] = new Variable(variables.size, sideEffectfulValues, sideEffects, dependencies, assignments)
      for (value <- sideEffectfulValues) {
        constraints += Reject(ret.varId, value)
      }
      variables.append(ret)
      _created += ret
      ret
    }

    def newConstraint(constraint: Constraint) {
      constraints += ConditionalConstraint(constraint, dependencies)
    }
  }

  /* Constraint wrappers */

  class InferenceWrapper extends Inference[ConstraintWrapper] {
    /** Creates a copy of the given constraint with its variables swapped out for other variables.
      *
      * @param constraint constraint to make a copy of
      * @param substitution keys will be constraint.coverage. values are the desired replacement variables
      * @return A copy of the given constraint, but with different variables.
      */
    def substitute[C <: ConstraintWrapper](constraint: C, substitution: Map[VarId, VarId]): ConstraintWrapper = constraint.substitute(substitution)
  }

  sealed trait ConstraintWrapper extends Revisable[Values, Value] {
    def substitute(substitution: Map[VarId, VarId]): ConstraintWrapper
  }

  case class ConditionalConstraint(inner: Constraint, dependencies: List[Assignment]) extends ConstraintWrapper {
    lazy val coverage = inner.coverage ++ (dependencies map { _._1 })

    def revise(rw: ReadWrite[Values, Value]): Boolean = {
      for (dependency <- dependencies.reverse) {
        if (!ranger.equals(rw.readVar(dependency._1), ranger.toSingleton(dependency._2))) {
          return true
        }
      }
      inner.revise(rw)
    }

    def substitute(substitution: Map[Int, Int]): ConstraintWrapper =
      ConditionalConstraint(domain.substitute(inner, substitution), dependencies.map(x => substitution(x._1) -> x._2))
  }

  case class Reject(vid: Int, value: Value) extends ConstraintWrapper {
    lazy val coverage = Set(vid)

    def revise(rw: ReadWrite[Values, Value]): Boolean = {
      rw.shrinkVar(vid, value)
      true
    }

    def substitute(substitution: Map[Int, Int]): ConstraintWrapper = copy(vid = substitution(vid))
  }

  case class Vanilla(inner: Constraint) extends ConstraintWrapper {
    lazy val coverage: Set[Int] = inner.coverage

    def revise(rw: ReadWrite[Values, Value]): Boolean = inner.revise(rw)

    def substitute(substitution: Map[Int, Int]): ConstraintWrapper = Vanilla(domain.substitute(inner, substitution))
  }
}

object DynamicSolver {
  def noSideEffects[Value](value: Value) { }
}


