package taffy.examples

import taffy._
import domains._
import domains.Addend
import domains.Eq
import domains.Equation
import domains.LtEq
import scala.collection.mutable
import taffy.ReadWrite.{Accepts, Is, Rejects}
import scala.{None, collection}
import collection.mutable.ArrayBuffer
import taffy.ReadWrite.Accepts
import taffy.ReadWrite.Is
import taffy.ReadWrite.Rejects

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/30/13
 * Time: 4:09 PM
 */

/*
I'm starting to think that the whole satisfiersOf and constraintsOf map is completely unnecessary.
Each constraint can be translated into a simple linear equation
   sat1 + sat2 + sat3 = 1 for exact and sat1 + sat2 + sat3 <= 1 for bounded
The revise function, then, won't even use constraintsOf and satisfiersOf... in fact, it shouldn't exist
at all! ExactCover should not extend Domain. ExactCover should just make use of BoundedSum

This is gonna be REALLY fast... that's one sophisticated learning function for arbitrary exact cover problems!

Sometimes combining equations will produce multiple new equations. e.g. if the resultant "equation"
requires that the sum be between 1 and 5, this can be expressed as two equations, one >= 1 and one <= 5.

Be careful about using negative multipliers, and be careful about adding equations that are bounded
in different directions.

And if all else fails, don't worry about generating a new equation!
 */
object ExactCover {
  def solve[Constraint, Satisfier](exact: Set[Constraint],  bounded: Set[Constraint],  getSatisfiers: Constraint => Set[Satisfier]): Option[Set[Satisfier]] = {
    val satisfiers: mutable.Set[Satisfier] = mutable.Set.empty
    for (constraint <- (exact ++ bounded)) {
      satisfiers ++= getSatisfiers(constraint)
    }
    val vars: mutable.Map[Satisfier, Int] = mutable.Map.empty
    val satisfierIndex: ArrayBuffer[Satisfier] = new ArrayBuffer()
    var i = 0
    for (satisfier <- satisfiers) {
      vars(satisfier) = i
      satisfierIndex += satisfier
      i += 1
    }
    var equations: Set[Equation] = Set.empty
    for (constraint <- exact) {
      equations = equations + Equation(getSatisfiers(constraint).toList.map(x => Addend(1, vars(x))), Eq(), 1)
    }
    for (constraint <- bounded) {
      equations = equations + Equation(getSatisfiers(constraint).toList.map(x => Addend(1, vars(x))), LtEq(), 1)
    }
    val domain = new BoundedSum(0, 1)
    val problem = new Problem[Equation, Set[Int], Int](vars.size, equations, Set(0, 1))
    val solver = new Solver[Equation, Set[Int], Int](domain, problem, new SetRanger())
    solver.solve() match {
      case None => None
      case Some(reader) =>
        var ret: Set[Satisfier] = Set.empty
        for (vid <- 0 until vars.size) {
          if (reader.read(vid) == 1) ret = ret + satisfierIndex(vid)
        }
        Some(ret)
    }
  }
}

object MatrixExactCover {
  def main(args: Array[String]) {
    // From the wikipedia page on exact cover:
    val a = Set(1, 4, 7)
    val b = Set(1, 4)
    val c = Set(4, 5, 7)
    val d = Set(3, 5, 6)
    val e = Set(2, 3, 6, 7)
    val f = Set(2, 7)

    // expected solution: b, d, f
    def getSatisfiers(constraint: Int): Set[Set[Int]] = {
      for (satisfier <- Set(a, b, c, d, e, f); if satisfier.contains(constraint)) yield satisfier
    }
    ExactCover.solve[Int, Set[Int]]((1 to 7).toSet, Set.empty, getSatisfiers) match {
      case None => throw new RuntimeException("could not find a solution")
      case Some(x) => if (!Set(b, d, f).equals(x)) throw new RuntimeException("unexpected solution: " + x)
    }
  }
}

object NQueens {
  abstract class Constraint
  case class Row(row: Int) extends Constraint
  case class Column(column: Int) extends Constraint
  case class ForwardSlash(diff: Int) extends Constraint
  case class BackwardSlash(sum: Int) extends Constraint

  def main(args: Array[String]) {
    val size = 8
//    val satisfiers: Set[(Int, Int)] = (for (i <- 0 until size; j <- 0 until size) yield { ((i, j)) }).toSet
    val exact: Set[Constraint] = ((0 until size).map(Row(_)) ++ (0 until size).map(Column(_))).toSet
    val bounded: Set[Constraint] = ((-(size-1) until size).map(ForwardSlash(_)) ++ (-(size-1) until size).map(BackwardSlash(_))).toSet
    def getSatisfiers(c: Constraint): Set[(Int, Int)] = {
      c match {
        case Row(r) => (for (c <- 0 until size) yield { ((r, c)) }).toSet
        case Column(c) => (for (r <- 0 until size) yield { ((r, c)) }).toSet
        case BackwardSlash(s) => (for (r <- 0 until size; if s - r >= 0 && s - r < size) yield { ((r, s - r)) }).toSet // incomplete
        case ForwardSlash(d) => (for (r <- 0 until size; if r + d >= 0 && r + d < size) yield { ((r, r + d)) }).toSet
      }
    }
    ExactCover.solve[Constraint, (Int, Int)](exact, bounded, getSatisfiers) match {
      case None =>
        println("no solution")
        if (size != 2 && size != 3) throw new RuntimeException("This is probably a bug!")
      case Some(spots) =>
        for (i <- 0 until size) {
          for (j <- 0 until size) {
            print(if (spots.contains((i, j))) "X" else ".")
          }
          println()
        }
    }
  }
}