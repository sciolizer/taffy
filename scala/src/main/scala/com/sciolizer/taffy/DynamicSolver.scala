package com.sciolizer.taffy

import util.control.Breaks._

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/15/13
 * Time: 11:32 AM
 */
class DynamicSolver[Constraint, Values, Value](domain: Domain[Constraint, Values, Value], ranger: Ranger[Values, Value]) {
  def solve[A, B](problem: Init[Constraint, Value] => A, solutionReader: (A, Reader[Value]) => B): Option[B] = {

  }
}

class Variable[Value](val varId: Int)

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