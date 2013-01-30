package taffy.examples

import taffy.{Problem, Solver, ReadWrite, Domain}
import scala.collection.mutable

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/29/13
 * Time: 4:08 PM
 */
case class Addend(coefficient: Int, variable: Int)
case class Equation(addends: List[Addend], sum: Int)
class ExactCover extends Domain[Equation, BVars, Boolean] {

  override def learn(firstUniqueImplicationPoint: ExactCover#VarId, constraints: List[(ExactCover#VarId, ExactCover#MixedConstraint)]): List[(Equation, List[ExactCover#MixedConstraint])] = List.empty

  def revise(rw: ReadWrite[Equation, BVars, Boolean], c: Equation): Boolean = {
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
          if (vals.candidates.head == coefficient > 0) {
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

  def coverage(c: Equation): collection.Set[ExactCover#VarId] = c.addends.map(_.variable).toSet
}

object ExactCover {
  def main(args: Array[String]) {
    val problem = new Problem[Equation, BVars, Boolean](3, Set(Equation(List(Addend(1, 0), Addend(1, 1), Addend(1, 2)), 1)), new BVars())
    val solver = new Solver(new ExactCover(), problem, new BVarRanger())
    solver.solve() match {
      case None => println("No solution found")
      case Some(reader) =>
        println("0: " + reader.read(0))
        println("1: " + reader.read(1))
        println("2: " + reader.read(2))
    }
  }
}

object TwoEquations {
  def main(args: Array[String]) {
    /*
    a + b + c = 1
    d + b + e = 1
    a + b + c + d + e = 1
    All variables are either 1 or 0.
    Solver should quickly identify that b = 1 and all others are zero.
    Resolution of equations should quickly identify b as a special case.
     */
    val problem = new Problem[Equation, BVars, Boolean](5,
      Set(Equation(List(Addend(1, 0), Addend(1, 1), Addend(1, 2)), 1),
          Equation(List(Addend(1, 3), Addend(1, 1), Addend(1, 4)), 1),
          Equation(List(Addend(1, 0), Addend(1, 1), Addend(1, 2), Addend(1, 3), Addend(1, 4)), 1)),
      new BVars())
    val solver = new Solver(new ExactCover(), problem, new BVarRanger())
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