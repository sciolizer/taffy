package taffy

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 9:27 AM
 */

import taffy._

trait Domain[Constraint, Variable] {
  type VarId = Int

  def learn(constraints : List[Constraint]) : List[(Constraint,List[Constraint])]

  def revise(rw : ReadWrite[Constraint,Variable], c: Constraint) : Boolean

  def coverage(c : Constraint) : List[VarId]
}
