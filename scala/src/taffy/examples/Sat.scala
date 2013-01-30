package taffy.examples

import taffy._
//import examples.Literal
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

class BVars(val candidates: Set[Boolean]) {
  def this() = this(Set(true, false))
  override def toString: String = {
    val sb = new StringBuilder()
    sb.append("[")
    if (candidates.contains(true)) sb.append("T")
    if (candidates.contains(false)) sb.append("F")
    sb.append("]")
    sb.toString()
  }

  override def hashCode(): Int = candidates.hashCode()

  override def equals(obj: Any): Boolean = candidates.equals(obj.asInstanceOf[BVars].candidates)
}

class BVarRanger extends Ranger[BVars, Boolean] {
  def pick(values: BVars): Boolean = values.candidates.head

  def toSingleton(value: Boolean): BVars = new BVars(Set(value))

  /**
   * Inverse of toSingleton. If the collection is not a singleton,
   * an error is raised. Caller is expected to know that the
   * given collection is a singleton. (e.g. after a constraint problem
   * has been successfully solved, every variable should have a singleton
   * of values.)
   * @param values A collection expected to be a singleton.
   * @return The single value in the given collection.
   */
  def fromSingleton(values: BVars): Boolean = if (isSingleton(values)) values.candidates.head else throw new RuntimeException("not a singleton")

  def isSingleton(values: BVars): Boolean = values.candidates.size == 1

  def intersection(left: BVars, right: BVars): BVars = new BVars(left.candidates.intersect(right.candidates))

  def subtraction(minuend: BVars, subtrahend: BVars): BVars = new BVars(minuend.candidates -- subtrahend.candidates)

  def isEmpty(values: BVars): Boolean = values.candidates.isEmpty
}

class Sat extends Domain[List[Literal], BVars, Boolean] {
  def learn(constraints: List[List[Literal]]): List[(List[Literal], List[List[Literal]])] = List.empty // todo

  def revise(rw: ReadWrite[List[Literal], BVars, Boolean], c: List[Literal]) : Boolean = {
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
    val problem = new Problem[List[Literal], BVars, Boolean](3, Set(clause0, clause1, clause2), new BVars(Set(true, false)))
    val s = new Solver(new Sat(), problem, new BVarRanger())
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