package com.sciolizer.taffy

import org.scalatest.FunSuite

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/15/13
 * Time: 12:04 PM
 */
class DynamicSolverSuite extends FunSuite {
  test("Compute the LCM of 6 and 8") {
    /*
    Problem: find two lists of numbers (henceforth called "left" and "right"), each of arbitrary finite length,
    such that their last elements are equal. The left list is some truncation of the sequence [6, 12, 18, 24 ...], and
    the right list is some truncation of the sequence [8, 16, 24, 36 ...].
     */
    abstract class Value
    case class ValueInt(value: Int) extends Value
    case class ValueList(isEmpty: Boolean) extends Value
    abstract class Constraint
    case class TypeIs(v: Variable[Value], expected: Class) extends Constraint
    case class ConditionallyEqualInts(left: Variable[Value], right: Variable[Value], list: Variable[Value], whenEmpty: Boolean) extends Constraint
    case class EqualInts(left: Variable[Value], right: Variable[Value]) extends Constraint
    case class ConstantInt(v: Variable[Value], i: Int) extends Constraint
    case class DifferenceOf(larger: Variable[Value], smaller: Variable[Value], diff: Int) extends Constraint

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

    def problem(init: Init[Constraint, Value]): String = {
      val left0 = init.newVariable()
      val leftLast0 = init.newVariable()

      val extendLeft = new SideEffects[Constraint, Value] {
        def run(variable: Variable[Value], value: Value, instantiator: Instantiator[Constraint, Value]) {
          if (value == ValueList(isEmpty = false)) {
            val local = instantiator.newVariable()
            val localLast = instantiator.newVariable()
            val localSize = instantiator.newVariable(extendLeft)
            instantiator.newConstraint(TypeIs(local, Class[ValueInt]))
            instantiator.newConstraint(TypeIs(localLast, Class[ValueInt]))
            instantiator.newConstraint(TypeIs(localSize, Class[ValueList]))
            instantiator.newConstraint(ConditionallyEqualInts(local, localLast, localSize, whenEmpty = true))
            instantiator.newConstraint(ConditionallyEqualInts(hm, local, variable, whenEmpty = false))
            instantiator.newConstraint(DifferenceOf(local, hm, 6))
          }
        }
      }
      val leftSize0 = init.newVariable(extendLeft)
    }
  }
}
