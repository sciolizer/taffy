package com.sciolizer.taffy

trait VariableInstantiator[Value] {

  def newVariable(sideEffectfulValues: Set[Value], sideEffects: (Variable[Value], Value) => Unit = DynamicSolver.noSideEffects[Value]): Variable[Value]

  def newVariableX(sideEffectfulValues: Set[Value], sideEffects: Value => Unit): Variable[Value] = {
    def effects(_v: Variable[Value], value: Value) { sideEffects(value) }
    newVariable(sideEffectfulValues, effects)
  }


}
