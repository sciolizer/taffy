package com.sciolizer.taffy.domains.lists

import com.sciolizer.taffy._

trait DynamicList[Values, Value] {
/*
  private[this] val isEmpty = solver.newVariable(Set(subsume(false)), sideEffects)
  solver.newConstraint

  def sideEffects(effect: Value) {
    if (ranger.equal(effect, ))
  }
  */
  /*
  Need to have side effects for when isEmpty is set to false
  Need to have a type constraint on isEmpty

   */

  /*
  val sideEffects: (Variable[Value], Value) => Unit = extend(local, localLast, diff)
  val localSize: Variable[Value] = ds.newVariable(Set[Value](ValueList(isEmpty = false)), sideEffects)
  ds.newConstraint(TypeIs(local, expectedInt = true))
  ds.newConstraint(TypeIs(localLast, expectedInt = true))
  ds.newConstraint(TypeIs(localSize, expectedInt = false))
  ds.newConstraint(ConditionallyEqualInts(local, localLast, localSize, whenEmpty = true))
  Triple(local, localLast, localSize)
  */

  def readWrite(rw: ReadWrite[Values, Value]): ReadsWritesList[Values]

}