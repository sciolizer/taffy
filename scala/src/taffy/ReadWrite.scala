package taffy

import taffy.ReadWrite.Contains
import collection.mutable

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 9:32 AM
 */

class ReadWrite[Constraint, Variables, Variable](constraint: Constraint,
                                                 variables: mutable.ArrayBuffer[Variables],
                                                 varsRead: mutable.Queue[Int],
                                                 undo: mutable.Queue[(Int, Variables)]) {
  type VarId = Int

  def readVar(v : VarId) : Set[Variable] = {
    throw new RuntimeException("not implemented")
  }

  /**
   * Similar to calling readVar and verifying that the returned set is a singleton
   * containing the given value. You should use this function, if you can,
   * instead of using readVar, since it communicates back to the solver,
   * "I am interested in this particular value", which means the solver can
   * execute a more efficient watched literal strategy.
   *
   * @param v The variable you want to read
   * @param value The value you hope the variable contains.
   * @return true iff the variable is currently a singleton with the given value. Returns false
   *         if either the variable has no values (meaning the problem is in a contradictory state),
   *         or if the variable still has at least two possible values that don't violate any
   *         constraints.
   */
  def contains(v : VarId, value : Variable) : Contains = {
    throw new RuntimeException("not implemented")
  }

  def setVar(v : VarId, value : Variable) {
    throw new RuntimeException("not implemented")
  }

  def intersectVar(v : VarId, values : Set[Variable]) {
    throw new RuntimeException("not implemented")
  }

  def shrinkVar(v : VarId, value : Variable) {
    throw new RuntimeException("not implemented")
  }
}

object ReadWrite {
  abstract class Contains
  case class Accepts() extends Contains
  case class Rejects() extends Contains
  case class Is() extends Contains
}