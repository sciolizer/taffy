package taffy

import taffy.ReadWrite.{Accepts, Is, Rejects, Contains}
import collection.mutable

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 9:32 AM
 */

class ReadWrite[Constraint, Variables, Variable](variables: mutable.ArrayBuffer[Variables],
                                                 varsRead: mutable.Map[Int, (Variables /* original */, Option[Set[Variable]] /* passed to contains */)],
                                                 undo: mutable.Map[Int, Variables],
                                                 ranger: Ranger[Variables, Variable]) {
  type VarId = Int

  // todo: do safety check with the coverage function
  def readVar(v : VarId) : Variables = {
    val ret: Variables = variables(v)
    varsRead.get(v) match {
      case None => varsRead(v) = (ret, None) // first read, so record snapshot
      case Some((_, None)) => // do nothing
      case Some((orig, Some(_))) => varsRead(v) = (orig, None) // subsequent read, so leave snapshot as is
    }
    ret
  }

  /**
   * Similar to calling readVar and verifying that the returned set is a singleton
   * containing the given value. You should use this function, if you can,
   * instead of using readVar, since it communicates back to the solver,
   * "I am interested in this particular value", which means the solver can
   * execute a more efficient watched literal strategy.
   *
   * todo: a safety check with the coverage function
   *
   * @param v The variable you want to read
   * @param value The value you hope the variable contains.
   * @return true iff the variable is currently a singleton with the given value. Returns false
   *         if either the variable has no values (meaning the problem is in a contradictory state),
   *         or if the variable still has at least two possible values that don't violate any
   *         constraints.
   */
  def contains(v : VarId, value : Variable) : Contains = {
    val candidates: Variables = variables(v)
    varsRead.get(v) match {
      case None => varsRead(v) = (candidates, Some(Set(value))) // todo: this is good for determining watched literals but bad for nogood generation... make sure that the code in solver completely ignores this value (at least until I improve the watchers logic; even then, for populating the reasons array buffer, Solver should use the previous variable assignment, NOT the value returned in this Option of varsRead
      case Some((_,None)) => // do nothing
      case Some((orig, Some(s))) => varsRead(v) = (orig, Some(s + value)) // todo: same problem as None case two lines up
    }
    if (ranger.isEmpty(ranger.intersection(candidates, ranger.toSingleton(value)))) {
      Rejects()
    } else if (ranger.isSingleton(candidates)) {
      Is()
    } else {
      Accepts()
    }
  }

  def setVar(v : VarId, value : Variable) {
    intersectVar(v, ranger.toSingleton(value))
  }

  def intersectVar(v : VarId, values : Variables) {
    replace(v, ranger.intersection(_, values))
  }

  def shrinkVar(v : VarId, value : Variable) {
    replace(v, ranger.subtraction(_, ranger.toSingleton(value)))
  }

  private def replace(v: VarId, replacer: Variables => Variables) {
    val original = variables(v)
    val replacement = replacer(original)
    variables(v) = replacement
    undo.get(v) match {
      case None => undo(v) = original
      case Some(_) => // do nothing; can't get more original than the original
    }
  }
}

object ReadWrite {
  abstract class Contains
  case class Accepts() extends Contains
  case class Rejects() extends Contains
  case class Is() extends Contains
}
