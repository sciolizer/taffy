package com.sciolizer.taffy

import collection.mutable
import collection.mutable.ArrayBuffer

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/15/13
 * Time: 11:32 AM
 */
class DynamicSolver[Constraint, Values, Value](domain: Domain[Constraint, Values, Value], ranger: Ranger[Values, Value], candidateValues: Values) {

  def getChildVariables(variable: Variable[Value]): List[Variable[Value]] = {
    throw new NotImplementedError()
  }

  private var varCounter = 0
  private val constraints: mutable.Set[Constraint] = mutable.Set.empty
  private val variables: ArrayBuffer[Variable[Value]] = ArrayBuffer()

  // Most of the time creates a new variable.
  // But if called from within a side effect, it might return an already existing variable.
  def newVariable(sideEffects: Value => Unit = DynamicSolver.noSideEffects[Value]): Variable[Value] = {
    val ret = new Variable(varCounter, sideEffects)
    variables.append(ret)
    varCounter += 1
    ret
  }

  def newConstraint(constraint: Constraint) {
    constraints += constraint
  }

  def solve(isomorphisms: Isomorphisms = NoIsomorphisms): Option[Map[Variable[Value], Value]] = {
    val p = new Problem[Constraint, Values, Value](varCounter, Set.empty ++ constraints, candidateValues, isomorphisms)
    val sss = new SuperSimpleSolver[Constraint, Values, Value](domain, p, ranger)
    sss.backtrackingSearch((0 until varCounter).map(x => x -> candidateValues).toMap) match {
      case None => throw new NotImplementedError() // need to run side effects
      case Some(solution) =>
        Some(solution.map(x => (variables(x._1), x._2)))
    }
  }
}

object DynamicSolver {
  def noSideEffects[Value](value: Value) { }
}

case class Variable[Value](val varId: Int, effects: Value => Unit)

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