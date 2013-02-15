package com.sciolizer.taffy

import collection.mutable

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/15/13
 * Time: 11:32 AM
 */
class DynamicSolver[Constraint, Values, Value](domain: Domain[Constraint, Values, Value], ranger: Ranger[Values, Value], candidateValues: Values) {
  def solve[A, B](problem: Init[Constraint, Value] => A, solutionReader: (A, Reader[Value]) => B): Option[B] = {
    val constraints: mutable.Set[Constraint] = mutable.Set.empty
    var varCounter = 0
    val init = new Init[Constraint, Value] {
      def newVariable(sideEffects: SideEffects[Constraint, Value]): Variable[Value] = {
        val ret: Variable[Value] = new Variable(varCounter, {
          throw new NotImplementedError()
//          sideEffects.run(ret, hm, init)
        })
        varCounter += 1
        ret
      }

      def newConstraint(constraint: Constraint) {
        constraints += constraint
      }

      def newTemplate[A](template: (Instantiator[Constraint, Value]) => A): Template[Constraint, Value, A] = throw new NotImplementedError()
    }

    val handle: A = problem(init)

    val p = new Problem[Constraint, Values, Value](varCounter, Set.empty ++ constraints, candidateValues, NoIsomorphisms) // todo: allow isomorphisms
    val sss = new SuperSimpleSolver[Constraint, Values, Value](domain, p, ranger)
    sss.backtrackingSearch((0 until varCounter).map(x => x -> candidateValues).toMap) match {
      case None => throw new NotImplementedError() // need to run side effects
      case Some(solution) =>
        val reader = new Reader[Value] {
          def read(vid: Int): Value = solution(vid)
        }
        Some(solutionReader(handle, reader))
    }
  }
}

class Variable[Value](val varId: Int, effects: => Unit)

trait Instantiator[Constraint, Value] {
  def newVariable(sideEffects: SideEffects[Constraint, Value] = noSideEffects): Variable[Value]
  def newConstraint(constraint: Constraint)
  lazy val noSideEffects: SideEffects[Constraint, Value] = new SideEffects[Constraint, Value] {
    def run(variable: Variable[Value], value: Value, instantiator: Instantiator[Constraint, Value]) { }
  }
}

trait Init[Constraint, Value] extends Instantiator[Constraint, Value] {
  def newTemplate[A](template: Instantiator[Constraint, Value] => A): Template[Constraint, Value, A]
}

trait Template[Constraint, Value, A] {
  def instantiate(inst: Instantiator[Constraint, Value]): A
}

trait SideEffects[Constraint, Value] {
  def run(variable: Variable[Value], value: Value, instantiator: Instantiator[Constraint, Value])
}