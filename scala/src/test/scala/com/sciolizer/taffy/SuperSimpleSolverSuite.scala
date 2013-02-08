package com.sciolizer.taffy

import com.sciolizer.taffy.domains.{Literal, Disjunction}
import org.scalatest.FunSuite
import org.scalatest.BeforeAndAfter

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/7/13
 * Time: 10:10 AM
 */
class SuperSimpleSolverSuite extends FunSuite with BeforeAndAfter {

  // a = True, b = True, c = True is only valid assignment
  val constraint0 /* a \/ b \/ c   */ = List(Literal(true, 0), Literal(true, 1), Literal(true, 2))
  val constraint1 /* ~a \/ ~b \/ c */ = List(Literal(false, 0), Literal(false, 1), Literal(true, 2))
  val constraint2 /* a \/ b        */ = List(Literal(true, 0), Literal(true, 1))
  val constraint3 /* ~a \/ b       */ = List(Literal(false, 0), Literal(true, 1))
  val constraint4 /* a             */ = List(Literal(true, 0))
  val problem = new Problem[List[Literal], Set[Boolean], Boolean](
    3,
    Set(constraint0, constraint1, constraint2, constraint3, constraint4),
    Set(true, false))
  val sss = new SuperSimpleSolver[List[Literal], Set[Boolean], Boolean](new Disjunction[Set[Boolean]](), problem, new SetRanger())

  test(".revise should return None for unsatisfiable constraint") {
    assert(sss.revise(constraint4, Map(0 -> Set(false))) === None)
  }

  test(".revise should return empty for satisfiable but non-deducible constraint") {
    assert(sss.revise(constraint2, Map.empty) === Some(Map.empty))
  }

  test(".revise should return deduction for deducible constraint") {
    assert(sss.revise(constraint4, Map.empty) === Some(Map(0 -> Set(true))))
  }

  test(".rejectors returns empty set for empty assignment") {
    assert(sss.rejectors(Map.empty) === Set.empty)
  }

  test(".rejectors returns empty set for arc-consistent assignment") {
    assert(sss.rejectors(Map(0 -> Set(true), 1 -> Set(true), 2 -> Set(true))) === Set.empty)
  }

  test(".rejectors returns all rejecting constraints for arc-consistent assignment") {
    assert(sss.rejectors(Map(0 -> Set(false))) === Set(constraint4))
  }

  test("subsetOf returns true for non-proper subsets") {
    assert(false)
  }
}
