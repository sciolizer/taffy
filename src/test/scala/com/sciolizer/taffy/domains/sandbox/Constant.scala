package com.sciolizer.taffy.domains.sandbox

import com.sciolizer.taffy.{ReadWrite, Revisable}

sealed abstract class Constant(val vid: Int) extends Revisable[Set[Int], Int] {

  lazy val coverage: Set[VarId] = Set(vid)

  def substitute(substitution: Map[VarId, VarId]): Constant = updatedVarId(substitution(vid))

  def updatedVarId(vid: VarId): Constant

}

case class Is(override val vid: Int, value: Int) extends Constant(vid) {

  def revise(rw: ReadWrite[Set[Int], Int]): Boolean = {
    rw.setVar(vid, value)
    true
  }

  def updatedVarId(vid: VarId): Constant = copy(vid = vid)

}

case class IsNot(override val vid: Int, value: Int) extends Constant(vid) {

  def revise(rw: ReadWrite[Set[Int], Int]): Boolean = {
    rw.shrinkVar(vid, value)
    true
  }

  def updatedVarId(vid: VarId): Constant = copy(vid = vid)

}