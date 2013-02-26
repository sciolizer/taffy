package com.sciolizer.taffy

import com.sciolizer.taffy.Variable.SolverRef
import collection.mutable

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/21/13
 * Time: 11:29 AM
 */
class Variable[Value](
    val varId: Int,
    sideEffectfulValues: Set[Value], // todo: get rid of this
    effects: Value => Unit,
    ancestors: List[Variable.Assignment[Value]],
    solver: SolverRef[Value]) {


  // todo: add a check to make sure that Value has a legitimate equals() and hashCode()
  private[this] val expanded: mutable.Map[Value, List[Variable[Value]]] = mutable.Map.empty

  def value: Value = solver.value(varId)

  def childVariables: List[Variable[Value]] = expanded(value)

  // todo: figure out how to hide this method (use traits)
  def requiresExpansion: Boolean = sideEffectfulValues.contains(value) && !expanded.contains(value)

  // todo: figure out how to hide this method. Obvious solution: use traits. (i.e. Make Variable a trait, instead of a class)
  // todo: remove this return value
  def expand(value: Value): Boolean = {
    var ret = false
    if (expanded.contains(value)) {
      throw new IllegalArgumentException("Variable has already been expanded for given value: " + value)
    } else {
      ret = true
      val newVariables: List[Variable[Value]] = solver.conditionedOn((varId -> value) +: ancestors) {
        effects(value)
      }
      expanded(value) = newVariables
    }
    ret
  }

  override def equals(obj: Any): Boolean = obj.isInstanceOf[Variable[Value]] && varId == obj.asInstanceOf[Variable[Value]].varId
  override def hashCode(): Int = varId.hashCode()
}

object Variable {
  type VarId = Int
  type Assignment[Value] = Tuple2[VarId, Value]

  trait SolverRef[Value] {
    def conditionedOn(dependencies: List[Assignment[Value]])(action: => Unit): List[Variable[Value]]
    def value(vid: VarId): Value
  }
}