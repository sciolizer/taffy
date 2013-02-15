package com.sciolizer.taffy.examples

import com.sciolizer.taffy._
import examples.ExactCover.SolverFactory
import com.sciolizer.taffy.domains._
import com.sciolizer.taffy.domains.Addend
import com.sciolizer.taffy.domains.Eq
import com.sciolizer.taffy.domains.Equation
import com.sciolizer.taffy.domains.LtEq
import scala.collection.mutable
import scala.{None, collection}
import collection.mutable.ArrayBuffer
import scala.Some

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

  trait SolverFactory[Satisfier] {
    def make(domain: BoundedSum,
             problem: Problem[Equation, Set[Int], Int],
             ranger: Ranger[Set[Int], Int],
             satisfierIndex: Array[Satisfier]): SuperSimpleSolver[Equation, Set[Int], Int]
  }

  def defaultSolverFactory[Satisfier](): SolverFactory[Satisfier] = {
    new SolverFactory[Satisfier] {
      def make(domain: BoundedSum,
               problem: Problem[Equation, Set[Int], Int],
               ranger: Ranger[Set[Int], Int],
               satisfierIndex: Array[Satisfier]): SuperSimpleSolver[Equation, Set[Int], Int]
      = new SuperSimpleSolver[Equation, Set[Int], Int](domain, problem, ranger)
    }
  }

  def solve[Constraint, Satisfier : ClassManifest](
    exact: Set[Constraint],
    bounded: Set[Constraint],
    getSatisfiers: Constraint => Set[Satisfier],
    solverFactory: SolverFactory[Satisfier] = defaultSolverFactory()): Option[Set[Satisfier]] = {
    val satisfiers: mutable.Set[Satisfier] = mutable.Set.empty
    for (constraint <- (exact ++ bounded)) {
      satisfiers ++= getSatisfiers(constraint)
    }
    val vars: mutable.Map[Satisfier, Int] = mutable.Map.empty
    val satisfierIndex: ArrayBuffer[Satisfier] = new ArrayBuffer[Satisfier]()
    var i = 0
    for (satisfier <- satisfiers) {
      vars(satisfier) = i
      satisfierIndex += satisfier
      i += 1
    }
    println("satisfierIndex: " + satisfierIndex.zip(0 until (satisfierIndex.size)).toMap)
    var equations: Set[Equation] = Set.empty
    for (constraint <- exact) {
      equations = equations + Equation(getSatisfiers(constraint).toList.map(x => Addend(1, vars(x))), Eq(), 1)
    }
    for (constraint <- bounded) {
      equations = equations + Equation(getSatisfiers(constraint).toList.map(x => Addend(1, vars(x))), LtEq(), 1)
    }
    val domain = new BoundedSum(0, 1)
    val problem = new Problem[Equation, Set[Int], Int](vars.size, equations, Set(0, 1), NoIsomorphisms)
//    val si: Array[Satisfier] = satisfierIndex.toArray[Satisfier.class] WTF?
    val si = new Array[Satisfier](satisfierIndex.length)
    satisfierIndex.copyToArray(si)
    val solver: SuperSimpleSolver[Equation, Set[Int], Int] = solverFactory.make(domain, problem, new SetRanger(), si) // todo: revert to ordinary solver (without sanity check)
    val initialAssignment: Map[Int, Set[Int]] = (0 until vars.size).map(vid => (vid -> problem.candidateValues)).toMap
    solver.backtrackingSearch(initialAssignment) match {
      case None => None
      case Some(assignment) =>
        Some[Set[Satisfier]](assignment.filter(_._2 == 1).toSet.map[Satisfier, Set[Satisfier]](x => satisfierIndex(x._1)))
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
    ExactCover.solve[Int, Set[Int]]((1 to 7).toSet, Set(), getSatisfiers, ExactCover.defaultSolverFactory() /* wtf? */) match {
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
    val bounded: Set[Constraint] = ((-(size-1) until size).map(ForwardSlash(_)) ++ (0 until (2 * size - 1)).map(BackwardSlash(_))).toSet
    def getSatisfiers(cs: Constraint): Set[(Int, Int)] = {
      cs match {
        case Row(r) => (for (c <- 0 until size) yield { ((r, c)) }).toSet
        case Column(c) => (for (r <- 0 until size) yield { ((r, c)) }).toSet
        case BackwardSlash(s) => (for (r <- 0 until size; if s - r >= 0 && s - r < size) yield { ((r, s - r)) }).toSet // incomplete
        case ForwardSlash(d) => (for (r <- 0 until size; if r + d >= 0 && r + d < size) yield { ((r, r + d)) }).toSet
      }
    }
    for (constraint <- exact) {
      println(constraint + ": " + getSatisfiers(constraint))
    }
    for (constraint <- bounded) {
      println(constraint + ": " + getSatisfiers(constraint))
    }
    val sf = new SolverFactory[(Int, Int)] {
      def make(domain: BoundedSum, problem: Problem[Equation, Set[Int], Int], ranger: Ranger[Set[Int], Int], satisfierIndex: Array[(Int, Int)]): SuperSimpleSolver[Equation, Set[Int], Int] = {
        new SuperSimpleSolver[Equation, Set[Int], Int](domain, problem, ranger) {
          /*
          override def sanityCheckNoGood(nogood: NoGood[Set[Int]], constraints: List[(VarId, MixedConstraint)]) {
            val rejectingAssignment: Map[(Int, Int), Boolean] = nogood.forbidden.toList.map(x => (satisfierIndex(x._1), single(x._2))).toMap
            satisfyingAssignments(rejectingAssignment, (exact ++ bounded).toList).find(x => true) match {
              case None =>
              case Some(a) =>
                showBoard(size, a)
                throw new IllegalStateException("nogood is " + rejectingAssignment + "\nbut solution exists.\n" )
            }
          }

          override def sanityCheckLearned(learned: List[(Equation, List[MixedConstraint])], constraints: List[(VarId, MixedConstraint)]) {
            super.sanityCheckLearned(learned, constraints)
          }

          def single[Int](s: Set[Int]): Boolean = {
            if (s.size == 1) (s.head == 1) else throw new RuntimeException("set is not a singleton")
          }

          def satisfyingAssignments(partial: Map[(Int, Int), Boolean], constraints: List[Constraint]): Iterator[Map[(Int, Int), Boolean]] = {
            if (constraints.isEmpty) {
              Iterator.single(partial)
            } else {
              val constraint: Constraint = constraints.head
              meets(constraint, partial, getSatisfiers(constraint)).flatMap(m => satisfyingAssignments(m, constraints.tail))
            }
          }

          def meets(constraint: Constraint, partial: Map[(Int, Int), Boolean], spots: Set[(Int, Int)]): Iterator[Map[(Int, Int), Boolean]] = {
            var count = 0
            for ((r, c) <- spots) {
              partial.get((r,c)) match {
                case None =>
                case Some(b) => if (b) count += 1
              }
            }
            if (count > 1) {
              Iterator.empty
            } else {
              val zeroed = spots.map(x => (x, false)).toMap ++ partial
              if (count == 1) {
                Iterator.single(zeroed)
              } else {
                (if (bounded.contains(constraint)) Iterator.single(zeroed) else Iterator.empty) ++
                (for ((r, c) <- spots; if partial.get((r,c)).isEmpty) yield {
                  zeroed + ((r,c) -> true) // this is not right; we need to zero out the remainder as well
                }).iterator
              }
            }
          } */
        }
      }
    }
    ExactCover.solve[Constraint, (Int, Int)](exact, bounded, getSatisfiers, sf) match {
      case None =>
        println("no solution")
        if (size != 2 && size != 3) throw new RuntimeException("This is probably a bug!")
      case Some(spots) => showBoard(size, spots.map(x => (x, true)).toMap)
        }
    }

    def showBoard(size: Int, spots: Map[(Int, Int), Boolean]) {
      for (i <- 0 until size) {
        for (j <- 0 until size) {
          spots.get((i, j)) match {
            case None => print("?")
            case Some(b) => print(if (b) "X" else ".")
          }
        }
        println()
    }
  }
}