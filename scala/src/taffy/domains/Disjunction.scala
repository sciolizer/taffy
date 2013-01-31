package taffy.domains

import taffy.{ReadWrite, Domain}
import taffy.ReadWrite.{Is, Accepts, Rejects}

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/31/13
 * Time: 10:11 AM
 */
class Disjunction[Booleans] extends Domain[List[Literal], Booleans, Boolean] {

  // Learn function does not need to be implemented, because nogood generation already covers it.

  def revise(rw: ReadWrite[Booleans, Boolean], c: List[Literal]) : Boolean = {
    var accepts: Option[(Int, Boolean)] = None
    for (Literal(expected, varId) <- c) {
      rw.contains(varId, expected) match {
        case Is() => /* println("is: " + varId); */ return true
        case Accepts() =>
          accepts match {
            case None => /* println("acceptable: " + varId); */ accepts = Some(varId, expected)
            case Some(_) => /* println("double accept: " + varId); */ return true // at least two variables are undetermined, so no deduction can yet be made
          }
        case Rejects() =>
      }
    }
    accepts match {
      case None => /* println("constraint unsatisfiable"); */ false
      case Some((vid, expected)) =>
        // println("deduced " + vid + " is " + expected)
        rw.setVar(vid, expected) // unit clause optimization
        true
    }
  }

  def coverage(c: List[Literal]): collection.Set[Int] = c.map(_.vid).toSet
}

case class Literal(expected: Boolean, vid: Int)