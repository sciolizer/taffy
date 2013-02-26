package com.sciolizer.taffy

import domains.lists._
import domains.lists.ConditionallyEqualInts
import domains.lists.DifferenceOf
import domains.lists.ValueList
import domains.sandbox.Is
import domains.sandbox.{Is, ConstantInference, Constant}
import org.scalatest.FunSuite

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/15/13
 * Time: 12:04 PM
 */
class DynamicSolverSuite extends FunSuite {

  test("Problem with no dynamic variables") {
    // Trivial domain where the only constraints are to set a variable to the value 2.
    case class IsTheNumberTwo(varId: Int) extends Revisable[Set[Int], Int] {

      lazy val coverage: Set[VarId] = Set(varId)

      def revise(rw: ReadWrite[Set[Int], Int]): Boolean = {
        rw.setVar(varId, 2)
        true
      }

    }

    object D extends Inference[IsTheNumberTwo] {

      def substitute[C <: IsTheNumberTwo](constraint: C, substitution: Map[D.VarId, D.VarId]): IsTheNumberTwo =
        IsTheNumberTwo(substitution(constraint.varId))

    }

    val ds = new DynamicSolver[IsTheNumberTwo, Set[Int], Int](D, new SetRanger(), Set(0, 1, 2, 3))
    ds.newVariable(Set.empty) /* var0 */
    val var1 = ds.newVariable(Set.empty)
    ds.newConstraint(IsTheNumberTwo(var1.varId))
    assert(ds.solve())
    assert(var1.value === 2)
  }

  test("One side effect") {
    val ds = new DynamicSolver[Constant, Set[Int], Int](ConstantInference, new SetRanger(), Set(0, 1, 2, 3))
    val var0 = ds.newVariable(Set(2), value => {
      if (value == 2) {
        val secondVariable = ds.newVariable(Set.empty)
        ds.newConstraint(Is(secondVariable.varId, 3))
      }
    })
    ds.newConstraint(Is(var0.varId, 2))
    assert(ds.solve())
    assert(var0.value === 2)
    val var1: Variable[Int] = var0.childVariables(0)
    assert(var1.value === 3)
  }

  test("Compute the LCM of 6 and 8") {
    /*
    Problem: find two lists of numbers (henceforth called "left" and "right"), each of arbitrary finite length,
    such that their last elements are equal. The left list is some truncation of the sequence [6, 12, 18, 24 ...], and
    the right list is some truncation of the sequence [8, 16, 24, 36 ...].
     */

    // We start with 6 variables:
    //   left0
    //   leftLast0
    //   leftSize0
    //  and likewise for the right list.

    // We then constrain them as follows:
    //   left0 is a ValueInt (TypeIs)
    //   leftLast0 is a ValueInt (TypeIs)
    //   leftSize0 is a ValueList (empty or not empty) (TypeIs)
    //   liftSize0 being empty implies that left0 == leftLast0 (ConditionallyEqualInts, whenEmpty = true)
    //  similarly for the right list.
    //  we also have one constraint bridging the two lists:
    //    leftLast0 == rightLast0 (EqualInts)
    //  and we constrain left0 to be 6 and right0 to be 8 (ConstantInt)

    // If leftSize is assigned the value "not-empty", then three new variables are created as a side effect:
    //   left1
    //   leftLast1
    //   leftSize1
    // and the following constraints are placed on them:
    //   left1 is a ValueInt (TypeIs)
    //   leftLast1 is a ValueInt (TypeIs)
    //   leftSize1 is a ValueList (empty or not-empty) (TypeIs)
    //   leftSize1 being empty implies that left1 == leftLast1 (ConditionallyEqualInts, whenEmpty = true)
    //   leftSize0 being non-empty implies that leftLast0 == leftLast1 (ConditionallyEqualInts, whenEmpty = false)
    //   left1 is 6 greater than left0 (DifferenceOf)
    //  similarly for right, except that right1 will be 8 greater than right0.

    // Rinse and repeat if leftSize1 is set to non-empty

    // The output solution should be [6, 12, 18, 24] and [8, 16, 24]. (leftLast[0-3] and rightLast[0-2] = 24)

    val numbers = (0 until 26).map(ValueInt(_)).toSet
    val lists = Set(ValueList(isEmpty = true), ValueList(isEmpty = false))
    val ds = new DynamicSolver[Constraint, Set[Value], Value](new NullInference, new SetRanger(), numbers ++ lists)

    case class Triple(local: Variable[Value], localLast: Variable[Value], localSize: Variable[Value])

    def extend(prev: Variable[Value], prevLast: Variable[Value], diff: Int)(self: Variable[Value], value: Value) {
      if (value == ValueList(isEmpty = false)) {
        val triple = make(diff)
        ds.newConstraint(ConditionallyEqualInts(prevLast, triple.local, self, whenEmpty = false))
        ds.newConstraint(DifferenceOf(triple.local, prev, diff))
      }
    }

    def make(diff: Int): Triple /* the head */ = {
      val local = ds.newVariable(Set.empty)
      val localLast = ds.newVariable(Set.empty)
      val sideEffects: (Variable[Value], Value) => Unit = extend(local, localLast, diff)
      val localSize: Variable[Value] = ds.newVariable(Set[Value](ValueList(isEmpty = false)), sideEffects)
      ds.newConstraint(TypeIs(local, expectedInt = true))
      ds.newConstraint(TypeIs(localLast, expectedInt = true))
      ds.newConstraint(TypeIs(localSize, expectedInt = false))
      ds.newConstraint(ConditionallyEqualInts(local, localLast, localSize, whenEmpty = true))
      Triple(local, localLast, localSize)
    }

    val left = make(6)
    val right = make(8)

    ds.newConstraint(EqualInts(left.localLast, right.localLast))

    assert(ds.solve())
    assert(24 === left.localLast.value)
  }

}
