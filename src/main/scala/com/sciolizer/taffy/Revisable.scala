package com.sciolizer.taffy

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/21/13
 * Time: 9:26 AM
 */
trait Revisable[Values, Value] {
  type VarId = Int
  def revise(rw: ReadWrite[Values, Value]): Boolean
  def coverage: Set[VarId]
}
