package taffy.examples

import taffy._
import examples.Literal
import taffy.ReadWrite.{Rejects, Is, Accepts}
import taffy.ReadWrite.Accepts
import taffy.ReadWrite.Is
import taffy.ReadWrite.Rejects

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 10:02 AM
 */
case class Literal(expected: Boolean, vid: Int)

class Sat extends Domain[List[Literal], Set[Boolean], Boolean] {
  def learn(constraints: List[List[Literal]]): List[(List[Literal], List[List[Literal]])] = List.empty // todo

  def revise(rw: ReadWrite[List[Literal], Set[Boolean], Boolean], c: List[Literal]) : Boolean = {
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

  def coverage(c: List[Literal]): List[Int] = c.map(_.vid)
}

object Sat {
  def main(args: Array[String]) {
    /*
    not a \/ not b \/ not c
    not a \/ b
    a \/ c
     */
    val a = 0
    val b = 1
    val c = 2
    val clause0 = List(Literal(false, a), Literal(false, b), Literal(false, c))
    val clause1 = List(Literal(false, a), Literal(true, b))
    val clause2 = List(Literal(true, a), Literal(true, c))
    val problem = new Problem[List[Literal], Set[Boolean], Boolean](3, Set(clause0, clause1, clause2), Set(true, false))
    val s = new Solver(new Sat(), problem, new SetRanger[Boolean]())
    val answer = s.solve()
    answer match {
      case None => println("No solution found")
      case Some(reader) =>
        println("a: " + reader.read(a))
        println("b: " + reader.read(b))
        println("c: " + reader.read(c))
    }
  }
}