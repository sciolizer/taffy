package com.sciolizer.taffy.examples

import com.sciolizer.taffy._

//import examples.Literal

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 10:02 AM
 */
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



object SatExample {      /*
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
    val problem = new Problem[List[Literal], BVars, Boolean](3, Set(clause0, clause1, clause2), new BVars(Set(true, false)), NoIsomorphisms)
    val s = new SolverSanityCheck[List[Literal], BVars, Boolean](new Inference[BVars](), problem, new BVarRanger())
    val answer = s.solve()
    answer match {
      case None => println("No solution found")
      case Some(reader) =>
        println("a: " + reader.read(a))
        println("b: " + reader.read(b))
        println("c: " + reader.read(c))
    }
  } */
}