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
                    /*
  // extends Domain[Equation, Set[Boolean], Boolean] {
{
//  val vars: Map[(Constraint, Satisfier), Int] = (for (c <- satisfiersOf.keys; s <- constraintsOf.keys) yield { ((c, s), nextId() )}).toMap

  val

  private def invert[A,B](in: Map[A, Set[B]]): Map[B, Set[A]] = {
    // really, a mutable map has got to be more efficient than this
    var ret: Map[B, Set[A]] = Map.empty[B, Set[A]].withDefaultValue(Set.empty[A])
    for ((k, vs) <- in) {
      for (v <- vs) {
        ret = ret.updated(v, ret(v) + k)
      }
    }
    ret
  }
           /*
  def revise(rw: ReadWrite[Constraint, Set[Boolean], Boolean], c: Constraint): Boolean = {
    // todo: small optimization: if constraint is bounded, and the first n-1 are possibly false,
    // then we can skip reading the last variable
    val undecided: mutable.Set[VarId] = mutable.Set.empty
    var trues = 0
    for (satisfier <- satisfiersOf(c)) {
      for (vid <- vars((c, satisfier))) {
        rw.contains(vid, true) match {
          case Rejects =>
          case Is =>
            trues += 1
            if (trues > 1) return false
          case Accepts =>
            undecided += vid
        }
      }
    }
    if (trues == 1) {
      for (vid <- undecided) {
        rw.setVar(vid, false)
      }
      true
    } else if (undecided.size == 0) {
      bounded.contains(c)
    } else {
      if (undecided.size == 1 && exact.contains(c)) rw.setVar(undecided.head, true)
      true
    }
  }

  def coverage(c: Constraint): collection.Set[VarId] = {
    satisfiersOf(c).map(x => vars((c, x)))
  }

  def solve(): Option[Set[Satisfier]] = {
    val problem = new Problem(vars.size, satisfiersOf.keys, Set(true, false))
    val solver = new Solver(this, problem, new SetRanger())
    solver.solve() match {
      case None => None
      case Some(reader) =>
        var ret = Set.empty

    }
  } */     */
object MatrixExactCover {

}