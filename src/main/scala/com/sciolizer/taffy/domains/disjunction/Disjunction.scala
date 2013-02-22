package com.sciolizer.taffy.domains.disjunction

import com.sciolizer.taffy.{ReadWrite, Revisable}
import com.sciolizer.taffy.ReadWrite.{Rejects, Accepts, Is}

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/21/13
 * Time: 5:13 PM
 */
case class Disjunction[Booleans](literals: List[Literal]) extends Revisable[Booleans, Boolean] {
  lazy val coverage: Set[Int] = literals.map(_.vid).toSet

  def revise(rw: ReadWrite[Booleans, Boolean]) : Boolean = {
    var accepts: Option[(Int, Boolean)] = None
    for (Literal(expected, varId) <- literals) {
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

  def substitute(substitution: Map[Int, Int]): Disjunction[Booleans] =
    Disjunction(literals.map(_.substitute(substitution)))
}
