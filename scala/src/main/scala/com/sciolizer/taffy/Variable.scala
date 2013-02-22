package com.sciolizer.taffy

import com.sciolizer.taffy.Variable.{Assignments, ContextContainer}
import collection.mutable

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/21/13
 * Time: 11:29 AM
 */
class Variable[+Value](
    val varId: Int,
    val sideEffectfulValues: Set[Value],
    effects: Value => Unit,
    ancestors: List[Variable.Assignment[Value]],
    assignments: Assignments[Value]) {

  private[this] val successfulAssignments: mutable.Set[Value] = mutable.Set.empty
  // todo: add a check to make sure that Value has a legitimate equals() and hashCode()
  private[this] val expanded: mutable.Map[Value, List[Variable[Value]]] = mutable.Map.empty

  def value: Value = assignments.value(varId)

  def childVariables: List[Variable[Value]] = expanded(value)

  // todo: figure out how to hide this method
  def succcessfulAssignment(value: Value) {
    successfulAssignments += value
  }

  // todo: figure out how to hide this method
  def expand(contextContainer: ContextContainer[Value]): Boolean = {
    var ret = false
    for (value <- successfulAssignments) {
      if (!expanded.contains(value)) {
        ret = true
        val newVariables: List[Variable[Value]] = contextContainer.conditionedOn((varId -> value) +: ancestors) {
          effects(value)
        }
        expanded += value -> newVariables
      }
    }
    ret
  }

  override def equals(obj: Any): Boolean = obj.isInstanceOf[Variable[Value]] && varId == obj.asInstanceOf[Variable[Value]].varId
  override def hashCode(): Int = varId.hashCode()
}

object Variable {
  type VarId = Int
  type Assignment[Value] = Tuple2[VarId, Value]

  trait ContextContainer[Value] {
    def conditionedOn(assignments: List[Assignment[Value]])(action: => Unit): List[Variable[Value]]
  }

  trait Assignments[+Value] {
    def value(vid: VarId): Value
  }
}