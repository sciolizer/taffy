package com.sciolizer.taffy.domains.lists

import com.sciolizer.taffy.{ReadWrite, Variable, Revisable}

sealed trait Constraint extends Revisable[Set[Value], Value]

case class TypeIs(v: Variable[Value], expectedInt: Boolean) extends Constraint {

  def revise(rw: ReadWrite[Set[Value], Value]): Boolean = {
    if (expectedInt) {
      rw.shrinkVar(v.varId, ValueList(isEmpty = true))
      rw.shrinkVar(v.varId, ValueList(isEmpty = false))
    } else {
      rw.intersectVar(v.varId, Set(ValueList(isEmpty = true), ValueList(isEmpty = false)))
    }
    true
  }

  lazy val coverage: Set[Int] = Set(v.varId)

}

case class ConditionallyEqualInts(left: Variable[Value], right: Variable[Value], list: Variable[Value], whenEmpty: Boolean) extends Constraint {

  def revise(rw: ReadWrite[Set[Value], Value]): Boolean = {
    if (rw.readVar(list.varId) != Set(ValueList(whenEmpty))) return true
    val leftVals = rw.readVar(left.varId)
    val rightVals = rw.readVar(right.varId)
    rw.intersectVar(left.varId, rightVals)
    rw.intersectVar(right.varId, leftVals)
    true
  }

  lazy val coverage: Set[Int] = Set(left.varId, right.varId, list.varId)

}

case class EqualInts(left: Variable[Value], right: Variable[Value]) extends Constraint {

  def revise(rw: ReadWrite[Set[Value], Value]): Boolean = {
    val leftVals = rw.readVar(left.varId)
    val rightVals = rw.readVar(right.varId)
    rw.intersectVar(left.varId, rightVals)
    rw.intersectVar(right.varId, leftVals)
    true
  }

  lazy val coverage: Set[Int] = Set(left.varId, right.varId)

}

case class ConstantInt(v: Variable[Value], i: Int) extends Constraint {

  def revise(rw: ReadWrite[Set[Value], Value]): Boolean = {
    rw.setVar(v.varId, ValueInt(i))
    true
  }

  lazy val coverage: Set[Int] = Set(v.varId)

}

case class DifferenceOf(larger: Variable[Value], smaller: Variable[Value], diff: Int) extends Constraint {

  def revise(rw: ReadWrite[Set[Value], Value]): Boolean = {
    val largerVals = rw.readVar(larger.varId)
    val smallerVals = rw.readVar(smaller.varId)
    rw.intersectVar(larger.varId, (for (ValueInt(i) <- smallerVals) yield ValueInt(i + diff)))
    rw.intersectVar(smaller.varId, (for (ValueInt(i) <- largerVals) yield ValueInt(i + diff)))
    true
  }

  lazy val coverage: Set[Int] = Set(larger.varId, smaller.varId)

}
