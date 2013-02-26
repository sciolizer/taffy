package com.sciolizer.taffy

import collection.mutable
import collection.mutable.{ListBuffer, ArrayBuffer}

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/15/13
 * Time: 11:32 AM
 */
class DynamicSolver[Constraint <: Revisable[Values, Value], Values, Value](domain: Inference[Constraint], ranger: Ranger[Values, Value], candidateValues: Values) {
  type VarId = Int
  type Assignment = Tuple2[VarId, Value]

  private[this] var instantiationContext: InstantiationContext = new InstantiationContext(List.empty)
  private[this] val variables: ArrayBuffer[Variable[Value]] = ArrayBuffer()
  private[this] val solver =
    new StackedSolver[ConstraintWrapper, Values, Value](new InferenceWrapper, ranger, candidateValues)

//  private var solution: Option[Map[VarId, Value]] = None

  // Most of the time creates a new variable.
  // But if called from within a side effect, it might return an already existing variable.
  def newVariable(sideEffectfulValues: Set[Value], sideEffects: Value => Unit = DynamicSolver.noSideEffects[Value]): Variable[Value] =
    instantiationContext.newVariable(sideEffectfulValues, sideEffects)

  def newConstraint(constraint: Constraint) { instantiationContext.newConstraint(constraint) }

  def solve(isomorphisms: Isomorphisms = NoIsomorphisms): Boolean = {
    if (isomorphisms != NoIsomorphisms) throw new NotImplementedError()
    while (true) {
      solver.solution match {
        case None =>
          return false
        case Some(_) =>
          val expansions: mutable.Map[Variable[Value], Value] = mutable.Map.empty
          var pushes = 0
          for (variable <- variables) {
            while (variable.requiresExpansion && !expansions.contains(variable)) {
              // Add a Reject constraint to see if it is actually necessary for this variable to have this value
              solver.push()
              solver.insertConstraint(Reject(variable.varId, variable.value))
              solver.solution match {
                case None =>
                  // Yes, it's necessary. Queue up the variable for expansion
                  expansions(variable) = variable.value
                  solver.pop()
                case Some(_) =>
                  // No, it's not necessary. while loop continues with a different value for the variable
                  pushes += 1
              }
            }
          }
          if (expansions.isEmpty) return true // All variables have been assigned values that do not require expansion.
          0 until pushes foreach { _ => solver.pop() } // Pop all of the Reject constraints we added.
          expansions foreach { kv => kv._1.expand(kv._2, contextContainer) } // Create new variables and constraints.
      }
    }
  }

  private[this] lazy val contextContainer: Variable.ContextContainer[Value] = new ContextContainer[Value] {
    def conditionedOn(dependencies: List[(Variable.VarId, Value)])(action: => Unit): List[Variable[Value]] = {
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

  /* Instantiation contexts */


  lazy val assignments: Variable.Assignments[Value] = new Assignments[Value] {
    def value(vid: Variable.VarId): Value = solver.solution match {
      case None => throw new IllegalStateException("No solution")
      case Some(sol) => sol(vid)
    }
  }

  class InstantiationContext(dependencies: List[Assignment]) {
    private[this] val _created: ListBuffer[Variable[Value]] = ListBuffer.empty

    def created: List[Variable[Value]] = _created.toList

    def newVariable(sideEffectfulValues: Set[Value], sideEffects: (Value) => Unit = DynamicSolver.noSideEffects[Value]): Variable[Value] = {
      val varId = solver.insertVariable()
      assert(varId == variables.size)
      val ret: Variable[Value] = new Variable(varId, sideEffectfulValues, sideEffects, dependencies, assignments)
      variables.append(ret)
      _created += ret
      ret
    }

    def newConstraint(constraint: Constraint) {
      solver.insertConstraint(ConditionalConstraint(constraint, dependencies))
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


