package com.sciolizer.taffy

import domains.sandbox.{IsNot, Is, ConstantInference, Constant}
import org.scalatest.FunSuite

class StackedSolverSuite extends FunSuite {

  test("No stacking") {
    val ss = new StackedSolver[Constant, Set[Int], Int](ConstantInference, new SetRanger(), Set(0, 1, 2, 3))
    val vid = ss.insertVariable()
    ss.insertConstraint(Is(vid, 2))
    assert(2 === ss.solution.get(0))
  }

  test("Simple stacking") {
    val ss = new StackedSolver[Constant, Set[Int], Int](ConstantInference, new SetRanger(), Set(0, 1, 2, 3))
    val vid1 = ss.insertVariable()
    ss.insertConstraint(Is(vid1, 1))
    assert(1 === ss.solution.get(vid1))
    ss.push()
    ss.insertConstraint(IsNot(vid1, 1))
    assert(None === ss.solution)
    ss.pop()
    assert(1 === ss.solution.get(vid1))
    ss.push()
    val vid2 = ss.insertVariable()
    ss.insertConstraint(Is(vid2, 2))
    assert(2 === ss.solution.get(vid2))
    assert(1 === ss.solution.get(vid1))
    ss.pop()
    assert(1 === ss.solution.get(vid1))
  }

  test("Conditional stacking") {
    // I subclass DynamicSolver so that I can get access to ConstraintWrapper.
    new DynamicSolver[Constant, Set[Int], Int](ConstantInference, new SetRanger(), Set(0, 1, 2, 3)) {

      val ss = solver
      val vid1 = ss.insertVariable()
      ss.insertConstraint(Vanilla(Is(vid1, 1)))
      assert(1 === ss.solution.get(vid1))
      ss.push()
      ss.insertConstraint(Reject(vid1, 1))
      assert(None === ss.solution)
      ss.pop()
      assert(1 === ss.solution.get(vid1))
      ss.push()
      val vid2 = ss.insertVariable()
      ss.insertConstraint(ConditionalConstraint(Is(vid2, 2), List(vid1 -> 1)))
      assert(2 === ss.solution.get(vid2))
      assert(1 === ss.solution.get(vid1))
      ss.pop()
      assert(1 === ss.solution.get(vid1))

    }
  }
}
