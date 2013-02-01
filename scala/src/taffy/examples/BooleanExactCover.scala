package taffy.examples

import taffy._
import domains.{Eq, Addend, Equation, BoundedSum}
import scala.collection.mutable
import scala.{collection, Some}
import scala.collection

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/29/13
 * Time: 4:08 PM
 */                         /*
class BooleanExactCover extends Domain[Equation, BVars, Boolean] {
  val boundedSum = new BoundedSum(0, 1)
  // todo: this is a special case of BoundedSum, so just delegate
  // to that implementation
//  override def learn(firstUniqueImplicationPoint: BooleanExactCover#VarId, constraints: List[(BooleanExactCover#VarId, BooleanExactCover#MixedConstraint)]): List[(Equation, List[BooleanExactCover#MixedConstraint])] = List.empty

  def revise(rw: ReadWrite[Equation, BVars, Boolean], c: Equation): Boolean = {
    val
    boundedSum.revise(rw, c)
    // todo: this algorithm is still incomplete; in a + b + c + d + e = 1, when it is discovered that
    // c is true, the rest should be put to false. Currently only d and e are put to false.
    val (positives, negatives) = c.addends.partition(_.coefficient > 0)
    var upper = positives.map(_.coefficient).sum
    var lower = negatives.map(_.coefficient).sum
    val settable = mutable.Set[VarId]()
    var writing = 0 // 1 means maximize, -1 means minimize
    def outOfBounds(): Boolean = {
      if ((c.sum > upper) || (c.sum < lower)) return true
      if (c.sum == upper) {
        writing = 1 // maximize sum on unset variables
      } else if (c.sum == lower) {
        writing = -1 // minimize sum on unset variables
      }
      false
    }
    for (Addend(coefficient, vid) <- c.addends) {
      if (outOfBounds()) return false
      if (coefficient == 0) {
        throw new RuntimeException("invalid equation: zero coefficient")
      } else {
        val vals = rw.readVar(vid)
        if (vals.candidates.size == 0) {
          throw new RuntimeException("invalid state: variable was already in a contradictory state")
        } else if (vals.candidates.size == 1) {
          if (vals.candidates.head == (coefficient > 0)) {
            // positive and var is set, or negative and var is not set.
            // lower is thus not as low as it could have been if this var had not been set
            lower += math.abs(coefficient)
          } else {
            // positive and var is not set, or negative and var is set
            // upper is thus not as high as it could have been if this var had not been set
            upper -= math.abs(coefficient)
          }
        } else {
          settable += vid
        }
      }
    }
    if (outOfBounds()) {
      false
    } else if (writing == 0) {
      true
    } else {
      for (Addend(coefficient, vid) <- c.addends) {
        if (settable.contains(vid)) {
          if (writing == -1) {
            rw.setVar(vid, coefficient < 0) // turn on all negatives and off all positives
          } else if (writing == 1) {
            rw.setVar(vid, coefficient > 0) // turn off all negatives and on all positives
          }
        }
      }
      true
    }
  }

  def coverage(c: Equation): collection.Set[BooleanExactCover#VarId] = c.addends.map(_.variable).toSet
}                      */

object BooleanExactCoverExample {
  def main(args: Array[String]) {
    val problem = new Problem[Equation, Set[Int], Int](3, Set(Equation(List(Addend(1, 0), Addend(1, 1), Addend(1, 2)), Eq(), 1)), Set(0, 1))
    val solver = new SolverSanityCheck[Equation, Set[Int], Int](new BoundedSum(0, 1), problem, new SetRanger())
    solver.solve() match {
      case None => println("No solution found")
      case Some(reader) =>
        println("0: " + reader.read(0))
        println("1: " + reader.read(1))
        println("2: " + reader.read(2))
    }
  }
}

object ThreeBooleanEquations {
  def main(args: Array[String]) {
    /*
    a + b + c = 1
    d + b + e = 1
    a + b + c + d + e = 1
    All variables are either 1 or 0.
    Solver should quickly identify that b = 1 and all others are zero.
    Resolution of equations should quickly identify b as a special case.
     */
    val problem = new Problem[Equation, Set[Int], Int](5,
      Set(Equation(List(Addend(1, 0), Addend(1, 1), Addend(1, 2)), Eq(), 1),
          Equation(List(Addend(1, 3), Addend(1, 1), Addend(1, 4)), Eq(), 1),
          Equation(List(Addend(1, 0), Addend(1, 1), Addend(1, 2), Addend(1, 3), Addend(1, 4)), Eq(), 1)),
      Set(0, 1))
    val solver = new SolverSanityCheck[Equation, Set[Int], Int](new BoundedSum(0, 1), problem, new SetRanger())
    solver.solve() match {
      case None => println("No solution found")
      case Some(reader) =>
        println("a: " + reader.read(0))
        println("b: " + reader.read(1))
        println("c: " + reader.read(2))
        println("d: " + reader.read(3))
        println("e: " + reader.read(4))
    }
  }
}

//case class IntVars(lower: Int, upper: Int) // lower >= 0 (inclusive), upper <= 100 (exclusive), lower <= upper. lower == upper implies empty range
/*
class IntRanger extends Ranger[Set[Int], Int] {
  def pick(values: Set[Int]): Int = values.head

  def toSingleton(value: Int): Set[Int] = Set(value)

  /**
   * Inverse of toSingleton. If the collection is not a singleton,
   * an error is raised. Caller is expected to know that the
   * given collection is a singleton. (e.g. after a constraint problem
   * has been successfully solved, every variable should have a singleton
   * of values.)
   * @param values A collection expected to be a singleton.
   * @return The single value in the given collection.
   */
  def fromSingleton(values: Set[Int]): Int = if (isSingleton(values)) values.head else throw new RuntimeException("int var not a singleton: " + values)

  def isSingleton(values: Set[Int]): Boolean = values.size == 1

  def intersection(left: Set[Int], right: Set[Int]): Set[Int] = left.intersect(right)

  def subtraction(minuend: Set[Int], subtrahend: Set[Int]): Set[Int] = minuend -- subtrahend /*{
    def asSet(iv: IntVars): Set[Int] = (iv.lower until iv.upper).toSet
    val m = asSet(minuend)
    val s = asSet(subtrahend)
    val diff = m -- s
    if (diff.isEmpty) return IntVars(0, 0)
    val ret: IntVars = IntVars(diff.min, diff.max + 1)
    val expected = asSet(ret)
    if (diff.equals(expected)) {
      ret
    } else {
      // solver guarantees that only intersections of picked
      // values and shrunk values will ever be subtracted. todo: Find
      // a way to clearly express this invariant in the documentation.
      // actually this is not true. e.g. in the ThreeIntEquations problem,
      // the solver generates the nogood: a != 0 or c != 0 or b != 2
      // This nogood is evaluated when a is zero and b is 0-5, which means
      // the nogood has to compute [0-5] - [2-3] and verify that it is not empty
      // so that the clause can be evaluated as true (but unable to deduce the value of c).
      throw new RuntimeException("subtraction does not produce a range")
    }     */
    // todo: replace with more efficient implementation
    /*
    if (isEmpty(subtrahend) || subtrahend.upper <= minuend.lower || subtrahend.lower >= minuend.upper) return minuend
    if (subtrahend.lower > minuend.lower && subtrahend.upper < minuend.upper) {
      // solver guarantees that only intersections of picked
      // values and shrunk values will ever be subtracted. todo: Find
      // a way to clearly express this invariant in the documentation.
      throw new RuntimeException("subtraction does not produce a range")
    } else if (subtrahend.lower >= minuend.lower) {
      if (subtrahend.upper >= minuend.upper) IntVars(0, 0) else IntVars(minuend.lower, subtrahend.lower)
    } else if (subtrahend.upper <= minuend.upper) {
      if (subtrahend.lower <= minuend.lower) IntVars(0, 0) else IntVars(subtrahend.upper + 1, minuend.upper)
    } else {
      minuend
    }
    */
  //}

  def isEmpty(values: Set[Int]): Boolean = values.isEmpty
}     */
        /*
object TestSubtraction {
  def main(args: Array[String]) {
    val r = new IntRanger()
    val minuend = IntVars(1, 4)
    def s(subtrahend: IntVars, difference: IntVars) {
      assert(difference.equals(r.subtraction(minuend, subtrahend)))
    }
    s(IntVars(0, 0), IntVars(1, 4))
    s(IntVars(0, 1), IntVars(1, 4))
    s(IntVars(0, 2), IntVars(2, 4))
    s(IntVars(0, 3), IntVars(3, 4))
    s(IntVars(0, 4), IntVars(0, 0))
    s(IntVars(0, 5), IntVars(0, 0))
    s(IntVars(1, 1), IntVars(1, 4))
    s(IntVars(1, 2), IntVars(2, 4))
    s(IntVars(1, 3), IntVars(3, 4))
    s(IntVars(1, 4), IntVars(0, 0))
    s(IntVars(1, 5), IntVars(0, 0))
    s(IntVars(2, 2), IntVars(1, 4))
    s(IntVars(2, 4), IntVars(1, 2))
    s(IntVars(2, 5), IntVars(1, 2))
    s(IntVars(3, 3), IntVars(1, 4))
    s(IntVars(3, 4), IntVars(1, 3))
    s(IntVars(3, 5), IntVars(1, 3))
    s(IntVars(4, 4), IntVars(1, 4))
    s(IntVars(4, 5), IntVars(1, 4))
    s(IntVars(5, 5), IntVars(1, 4))
    assert(IntVars(0, 1).equals(r.subtraction(IntVars(0, 1), IntVars(0, 0))))
  }
}         */

object ThreeIntEquations {
  def main(args: Array[String]) {
    /*
    a + b + c = 5
    a + d + e = 5
    a + b + c + d + e = 5
    All variables are either 1 or 0.
    Solver should quickly identify that b = 5 and all others are zero.
    No good generation is insufficient to do this; we need to implement the learn function
    on the domain.
     */
    val cap = 3
    val problem = new Problem[Equation, Set[Int], Int](5,
      Set(Equation(List(Addend(1, 0), Addend(1, 1), Addend(1, 2)), Eq(), cap),
        Equation(List(Addend(1, 0), Addend(1, 3), Addend(1, 4)), Eq(), cap),
        Equation(List(Addend(1, 0), Addend(1, 1), Addend(1, 2), Addend(1, 3), Addend(1, 4)), Eq(), cap)),
      (0 to cap).toSet)
    val solver = new SolverSanityCheck[Equation, Set[Int], Int](new BoundedSum(0, cap), problem, new SetRanger())
    solver.solve() match {
      case None => println("No solution found")
      case Some(reader) =>
        println("a: " + reader.read(0))
        println("b: " + reader.read(1))
        println("c: " + reader.read(2))
        println("d: " + reader.read(3))
        println("e: " + reader.read(4))
    }
  }
}

object LightUp {
  /*
  Problem:
  . 0 . . . . .     00    01 02 03 04 05
  . . . . X . 0     06 07 08 09    10
  . 0 . . . . .     11    12 13 14 15 16
  . . . 3 . . .     17 18 19    20 21 22
  . . . . . 1 .     23 24 25 26 27    28
  1 . 1 . . . .        29    30 31 32 33
  . . . . . 1 .     34 35 36 37 38    39

  Each . is either on or off. Every . that is on (is a light) causes all . vertically and horizontally to be "lit". It does
  not cause . to be lit if they are on the other side of a number or an X.

  A valid solution:
    - causes all . to be lit
    - no lights are causing each other to be lit
    - every number is bordered above, below, to the left, and to the right, by exactly that number of lights.

  Here is the solution. Lights are represented by O. Variable names are to the right

  . 0 . . O . .
  O . . . X . 0
  . 0 . O . . .
  . . O 3 . O .
  . . . O . 1 .
  1 O 1 . . . O
  . . . . O 1 .
   */
  def main(args: Array[String]) {

  }
}