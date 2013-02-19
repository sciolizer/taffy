package com.sciolizer.taffy

import org.scalatest.FunSuite
import scala.collection

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/15/13
 * Time: 12:04 PM
 */
class DynamicSolverSuite extends FunSuite {
  test("Problem with no dynamic variables") {
    // Trivial domain where the only constraints are to set a variable to the value 2.
    object D extends Domain[Int, Set[Int], Int] {
      def revise(rw: ReadWrite[Set[Int], Int], c: Int): Boolean = { rw.setVar(c, 2); true }
      def coverage(c: Int): collection.Set[D.VarId] = Set(c)
      def substitute(c: Int, substitution: Map[D.VarId, D.VarId]): Int = substitution(c)
    }
    val ds = new DynamicSolver[Int, Set[Int], Int](D, new SetRanger(), Set(0, 1, 2, 3))
    ds.newVariable() /* var0 */
    val var1 = ds.newVariable()
    ds.newConstraint(var1.varId)
    assert(ds.solve().get(var1) === 2)
  }

  test("One side effect") {
    case class Constant(vid: Int, value: Int)
    object D extends Domain[Constant, Set[Int], Int] {
      def revise(rw: ReadWrite[Set[Int], Int], c: Constant): Boolean = { rw.setVar(c.vid, c.value); true }
      def coverage(c: Constant): collection.Set[D.VarId] = Set(c.vid)
      def substitute(c: Constant, substitution: Map[D.VarId, D.VarId]): Constant = c.copy(vid = substitution(c.vid))
    }
    val ds = new DynamicSolver[Constant, Set[Int], Int](D, new SetRanger(), Set(0, 1, 2, 3))
    val var0 = ds.newVariable(value => {
      if (value == 2) {
        val secondVariable = ds.newVariable()
        ds.newConstraint(Constant(secondVariable.varId, 3))
      }
    })
    val solution = ds.solve().get
    assert(solution(var0) === 2)
    val var1: Variable[Int] = ds.getChildVariables(var0)(0)
    assert(solution(var1) === 3)
  }
/*
  test("Compute the LCM of 6 and 8") {
    /*
    Problem: find two lists of numbers (henceforth called "left" and "right"), each of arbitrary finite length,
    such that their last elements are equal. The left list is some truncation of the sequence [6, 12, 18, 24 ...], and
    the right list is some truncation of the sequence [8, 16, 24, 36 ...].
     */
    abstract class Value
    case class ValueInt(value: Int) extends Value
    case class ValueList(isEmpty: Boolean) extends Value
    abstract class Constraint {
      def revise(rw: ReadWrite[Set[Value], Value]): Boolean
      val coverage: Set[Int]
    }
    case class TypeIs(v: Variable[Value], expectedInt: Boolean) extends Constraint {
      def revise(rw: ReadWrite[Set[Value], Value]): Boolean = {
        if (expectedInt) {
          rw.shrinkVar(v.varId, ValueList(isEmpty = true))
          rw.shrinkVar(v.varId, ValueList(isEmpty = false))
        } else {
          rw.intersectVar(v.varId, Set(ValueList(isEmpty = true), ValueList(isEmpty = false)))
        }
        true
      }
      lazy val coverage: Set[Int] = Set(v.varId)
    }
    case class ConditionallyEqualInts(left: Variable[Value], right: Variable[Value], list: Variable[Value], whenEmpty: Boolean) extends Constraint {
      def revise(rw: ReadWrite[Set[Value], Value]): Boolean = {
        if (rw.readVar(list.varId) != Set(ValueList(whenEmpty))) return true
        val leftVals = rw.readVar(left.varId)
        val rightVals = rw.readVar(right.varId)
        rw.intersectVar(left.varId, rightVals)
        rw.intersectVar(right.varId, leftVals)
        true
      }

      lazy val coverage: Set[Int] = Set(left.varId, right.varId, list.varId)
    }
    case class EqualInts(left: Variable[Value], right: Variable[Value]) extends Constraint {
      def revise(rw: ReadWrite[Set[Value], Value]): Boolean = {
        val leftVals = rw.readVar(left.varId)
        val rightVals = rw.readVar(right.varId)
        rw.intersectVar(left.varId, rightVals)
        rw.intersectVar(right.varId, leftVals)
        true
      }

      lazy val coverage: Set[Int] = Set(left.varId, right.varId)
    }
    case class ConstantInt(v: Variable[Value], i: Int) extends Constraint {
      def revise(rw: ReadWrite[Set[Value], Value]): Boolean = {
        rw.setVar(v.varId, ValueInt(i))
        true
      }

      lazy val coverage: Set[Int] = Set(v.varId)
    }
    case class DifferenceOf(larger: Variable[Value], smaller: Variable[Value], diff: Int) extends Constraint {
      def revise(rw: ReadWrite[Set[Value], Value]): Boolean = {
        val largerVals = rw.readVar(larger.varId)
        val smallerVals = rw.readVar(smaller.varId)
        rw.intersectVar(larger.varId, (for (ValueInt(i) <- smallerVals) yield ValueInt(i + diff)))
        rw.intersectVar(smaller.varId, (for (ValueInt(i) <- largerVals) yield ValueInt(i + diff)))
        true
      }

      lazy val coverage: Set[Int] = Set(larger.varId, smaller.varId)
    }

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

    def problem(init: Init[Constraint, Value]): Variable[Value] = {
      case class Triple(local: Variable[Value], localLast: Variable[Value], localSize: Variable[Value])
      def make(instantiator: Instantiator[Constraint, Value], diff: Int): Triple /* the head */ = {
        val local = instantiator.newVariable()
        val localLast = instantiator.newVariable()
        val localSize = instantiator.newVariable(extend(local, localLast, diff))
        instantiator.newConstraint(TypeIs(local, expectedInt = true))
        instantiator.newConstraint(TypeIs(localLast, expectedInt = true))
        instantiator.newConstraint(TypeIs(localSize, expectedInt = false))
        instantiator.newConstraint(ConditionallyEqualInts(local, localLast, localSize, whenEmpty = true))
        Triple(local, localLast, localSize)
      }

      def extend(prev: Variable[Value], prevLast: Variable[Value], diff: Int): SideEffects[Constraint, Value] = new SideEffects[Constraint, Value] {
        def run(variable: Variable[Value], value: Value, instantiator: Instantiator[Constraint, Value]) {
          if (value == ValueList(isEmpty = false)) {
            val triple = make(instantiator, diff)
            instantiator.newConstraint(ConditionallyEqualInts(prevLast, triple.local, variable, whenEmpty = false))
            instantiator.newConstraint(DifferenceOf(triple.local, prev, diff))
          }
        }
      }

      val left = make(init, 6)
      val right = make(init, 8)

      init.newConstraint(EqualInts(left.localLast, right.localLast))

      left.localLast // todo: figure out how I could reconstruct the entire list; just returning the last value seems like a limited use case
    }

    object D extends Domain[Constraint, Set[Value], Value] {
      def revise(rw: ReadWrite[Set[Value], Value], c: Constraint): Boolean = c.revise(rw)

      def coverage(c: Constraint): collection.Set[D.VarId] = c.coverage

      // Substitution will always contain keys for at least everything in coverage.
      def substitute(c: Constraint, substitution: Map[D.VarId, D.VarId]): Constraint = throw new RuntimeException("There are no isomorphisms.")
    }
    val numbers = (0 until 26).map(ValueInt(_)).toSet
    val lists = Set(ValueList(isEmpty = true), ValueList(isEmpty = false))
    val ds = new DynamicSolver[Constraint, Set[Value], Value](D, new SetRanger(), numbers ++ lists)

    def reader(v: Variable[Value], reader: Reader[Value]): Int = {
      reader.read(v.varId) match {
        case ValueInt(i) => i
        case _ => throw new IllegalStateException("TypeIs constraint was not satisfied.")
      }
    }

    assert(24 === ds.solve(problem, reader))
  } */
}
