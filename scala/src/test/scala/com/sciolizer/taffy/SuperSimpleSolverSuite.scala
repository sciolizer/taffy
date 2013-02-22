package com.sciolizer.taffy

import domains.disjunction.{Literal, Inference}
import org.scalatest.FunSuite
import org.scalatest.BeforeAndAfter
import scala.collection

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/7/13
 * Time: 10:10 AM
 */
class SuperSimpleSolverSuite extends FunSuite with BeforeAndAfter {
                                                                                /*
  // a = True, b = True, c = True is only valid assignment
  val constraint0 /* a \/ b \/ c   */ = List(Literal(true, 0), Literal(true, 1), Literal(true, 2))
  val constraint1 /* ~a \/ ~b \/ c */ = List(Literal(false, 0), Literal(false, 1), Literal(true, 2))
  val constraint2 /* a \/ b        */ = List(Literal(true, 0), Literal(true, 1))
  val constraint3 /* ~a \/ b       */ = List(Literal(false, 0), Literal(true, 1))
  val constraint4 /* a             */ = List(Literal(true, 0))
  val problem = new Problem[List[Literal], Set[Boolean], Boolean](
    3,
    Set(constraint0, constraint1, constraint2, constraint3, constraint4),
    Set(true, false),
    NoIsomorphisms)
  val sss = new SuperSimpleSolver[List[Literal], Set[Boolean], Boolean](new Inference[Set[Boolean]](), problem, new SetRanger())
  val initialAssignment: SuperSimpleSolver.PartialAssignment[Set[Boolean]] = (0 until 3).map(vid => vid -> problem.candidateValues).toMap

  test(".maintainArcConsistenty should fail on inconsistent assignment") {
    val prop = sss.newConsistencySustainer(initialAssignment ++ Map[Int, Set[Boolean]](0 -> Set()))
    assert(prop.rejector === Some(Right(constraint4)))
  }
  test(".revise should return None for unsatisfiable constraint") {
    assert(sss.revise(Right(constraint4), Map(0 -> Set(false))) === None)
  }

  test(".revise should return empty for satisfiable but non-deducible constraint") {
    assert(sss.revise(Right(constraint2), initialAssignment) === Some(Map.empty))
  }

  test(".revise should return deduction for deducible constraint") {
    assert(sss.revise(Right(constraint4), initialAssignment) === Some(Map(0 -> Set(true))))
  }

  test(".maintainArcConsistency should deduce solution") {
    // Same as problem above, but constraint 4 is removed.
    val problem = new Problem[List[Literal], Set[Boolean], Boolean](
      3,
      Set(constraint0, constraint1, constraint2, constraint3),
      Set(true, false),
      NoIsomorphisms)
    val sss = new SuperSimpleSolver[List[Literal], Set[Boolean], Boolean](new Inference[Set[Boolean]](), problem, new SetRanger())
    val sustainer = sss.newConsistencySustainer(initialAssignment ++ Map(0 -> Set(true)))
    assert(sustainer.implication === Map(0 -> Set(true), 1 -> Set(true), 2 -> Set(true)))
  }

  test("Order domain values") {
    assert(sss.orderDomainValues(0, initialAssignment).toSet === Set(true, false))
  }

  test("Complete assignment") {
    assert(sss.completeAssignment(initialAssignment ++ Map(0 -> Set(true))) === None)
    assert(sss.completeAssignment(Map(0 -> Set(false), 1 -> Set(true), 2 -> Set(false))) === Some(Map(0 -> false, 1 -> true, 2 -> false)))
  }

  test("Backtracking search") {
    assert(sss.backtrackingSearch(initialAssignment ++ Map(0 -> Set(false))) === None)
    assert(sss.backtrackingSearch(initialAssignment) === Some(Map(0 -> true, 1 -> true, 2 -> true)))
  }

  test("minimize") {
    val minimized = sss.minimize(initialAssignment ++ Map(0 -> Set(false), 1 -> Set(false)))
    assert(minimized.subsetOf(Set(Set(0), Set(1))))
  }

  test("noGood generation") {
    assert(sss.backtrackingSearch(initialAssignment ++ Map(0 -> Set(false), 1 -> Set(false))) === None)
    // Even though var 2 ('c' in the examples above) is not "given" as an argument to backtrackingSearch,
    // propagation (maintainArcConsistency) will add it to the conflictingAssignment, and so it will
    // be discovered as its own minimal conflict.
    assert(sss.learned === Set(Left(new NoGood(Map(0 -> Set(false)))), Left(new NoGood(Map(1 -> Set(false)))), Left(new NoGood(Map(2 -> Set(false))))))
  }

  object AllZeroes extends Inference[Int, Set[Int], Int] {
    def revise(rw: ReadWrite[Set[Int], Int], c: Int): Boolean = { rw.setVar(c, 0); true }
    def coverage(c: Int): collection.Set[AllZeroes.VarId] = Set(c)
    def substitute(c: Int, substitution: Map[AllZeroes.VarId, AllZeroes.VarId]): Int = substitution(c)
  }

  test("Duplicate writes are not mistaken as revisions") {
    val p = new Problem[Int, Set[Int], Int](2, Set(0, 1, 2), Set(0, 1, 2), NoIsomorphisms)
    val sss = new SuperSimpleSolver[Int, Set[Int], Int](AllZeroes, p, new SetRanger())
    assert(sss.revise(Right(0), Map(0 -> Set(0), 1 -> Set(0, 1, 2))) === Some(Map.empty))
  }

  test("Empty candidate values count as failure") {
    val p = new Problem[Int, Set[Int], Int](2, Set(0, 1, 2), Set(0, 1, 2), NoIsomorphisms)
    val sss = new SuperSimpleSolver[Int, Set[Int], Int](AllZeroes, p, new SetRanger())
    assert(sss.revise(Right(0), Map(0 -> Set(1), 1 -> Set(0, 1, 2))) === None)
  }
*/
}
