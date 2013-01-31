package taffy.domains

import scala.collection.mutable
import taffy._
import domains.Addend
import domains.Eq
import domains.Equation
import domains.GtEq
import domains.LtEq
import scala.Some
import scala.Right

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/31/13
 * Time: 10:16 AM
 *
 */
class BoundedSum(minimum: Int, maximum: Int /*, ordering: WellOrdered */) extends Domain[Equation, Set[Int], Int] {
  if (minimum < 0) throw new IllegalArgumentException("Negative minimums is not currently supported: " + minimum)
  if (minimum > maximum) throw new IllegalArgumentException("maximum " + maximum + "must be greater than minimum " + minimum)

                                  /*
  override def learn(constraints: List[(VarId, Option[MixedConstraint])]): List[(Equation, List[MixedConstraint])] = {
    val vars = constraints.map(_._1).toSet
    val cs = (for ((_, Some(Right(eq))) <- constraints) yield { eq }).toSet.toArray
    println("to learn: " + cs.toList)
    var ret: mutable.Map[Equation, List[MixedConstraint]] = mutable.Map.empty
    def toMap(eq: Equation): Map[VarId, Int] = eq.addends.map(x => (x.variable, x.coefficient)).toMap
    for (i <- 0 until cs.size - 1) {
      val eq1: Equation = cs(i)
      val eq1map = toMap(eq1)
      for (j <- i + 1 until cs.size) {
        val eq2: Equation = cs(j)
        val eq2map = toMap(eq2)
        for (v <- vars) {
          if (eq1map.contains(v) && eq2map.contains(v)) {
            val eq1coefficient = eq1map(v)
            val eq2coefficient = eq2map(v)
            var learnedSum: mutable.Map[VarId, Int] = mutable.Map.empty.withDefaultValue(0)
            def include(eq: Map[VarId, Int], multiplier: Int) {
              for ((vid, coef) <- eq) {
//                learnedSum(vid) += coef * multiplier // black magic
                learnedSum(vid) = learnedSum(vid) + coef * multiplier
              }
            }
            include(eq1map, -eq2coefficient)
            include(eq2map, eq1coefficient)
            val addends = (for ((vid, coeff) <- learnedSum; if coeff != 0) yield { Addend(coeff, vid) }).toList
            ret(Equation(addends, eq1.sum * -eq2coefficient + eq2.sum * eq1coefficient)) = List(Right(eq1), Right(eq2))
          }
        }
      }
    }
    println("learned: " + ret)
    ret.toList
  }          */

  def revise(rw: ReadWrite[Set[Int], Int], e: Equation): Boolean = {
    val (positives, negatives) = e.addends.partition(_.coefficient > 0)
    var upper = positives.map(_.coefficient * maximum).sum
    var lower = negatives.map(_.coefficient * maximum).sum
    val settable = mutable.Map[VarId, Set[Int]]()
    def outOfBounds(l: Int, u: Int): Boolean = {
      def lteq(): Boolean = l > e.sum
      def gteq(): Boolean = u < e.sum
      e.relation match {
        case Eq() => lteq() || gteq()
        case LtEq() => lteq()
        case GtEq() => gteq()
      }
    }
    def adjustedRange(coefficient: Int, minval: Int, maxval: Int, origMinVal: Int, origMaxVal: Int): (Int, Int) = {
      val minAdjustment = math.abs(coefficient * (minval - origMinVal))
      val maxAdjustment = math.abs(coefficient * (maxval - origMaxVal))
      if (coefficient > 0) {
        ((lower + minAdjustment, upper - maxAdjustment))
      } else {
        ((lower + maxAdjustment, upper - minAdjustment))
      }
    }
    for (Addend(coefficient, vid) <- e.addends) {
      if (outOfBounds(lower, upper)) return false
      if (coefficient == 0) {
        throw new RuntimeException("invalid equation: zero coefficient")
      } else {
        val vals = rw.readVar(vid)
        if (vals.isEmpty) {
          throw new RuntimeException("invalid state: variable was already in a contradictory state")
        } else {
          val adjusted: (Int, Int) = adjustedRange(coefficient, vals.min, vals.max, minimum, maximum)
          lower = adjusted._1
          upper = adjusted._2
//          (lower, upper) = adjustedRange(coefficient, vals.min, vals.max)
          if (vals.size > 1) settable += ((vid, vals))
        }
      }
    }
    if (outOfBounds(lower, upper)) {
      false
    } else {
      for (Addend(coefficient, vid) <- e.addends) {
        settable.get(vid) match {
          case None =>
          case Some(vals) =>
            for (value <- vals) { // todo: find a faster way to do this
              val (l, u) = adjustedRange(coefficient, value, value, vals.min, vals.max)
              if (outOfBounds(l, u)) rw.shrinkVar(vid, value)
            }
        }
      }
      true
    }
  }

  def coverage(c: Equation): collection.Set[BoundedSum#VarId] = c.addends.map(_.variable).toSet
}

case class Addend(coefficient: Int, variable: Int)
case class Equation(addends: List[Addend], relation: Relation, sum: Int)
abstract class Relation
case class Eq() extends Relation
case class LtEq() extends Relation
case class GtEq() extends Relation

object TestBoundedSum {
  type MixedConstraint = Either[NoGood[Set[Int]], Equation]
  def main(args: Array[String]) {
    {
      val rw = new ReadWriteMock[Set[Int], Int](Map(0 -> Set(0), 1 -> Set(0, 1, 2), 2 -> Set(1)), new SetRanger())
      val bs = new BoundedSum(0, 2)
      assert(bs.revise(rw, Equation(List(Addend(1, 0), Addend(1, 1), Addend(1, 2)), Eq(), 2)))
      val expected: Map[Int, Set[Int]] = Map[Int, Set[Int]](1 -> Set[Int](1))
      assert(rw.changes.equals(expected))
    }

    {
      val rw = new ReadWriteMock[Set[Int], Int](Map(0 -> Set(0), 1 -> Set(2), 2 -> Set(1), 3 -> Set(2), 4 -> Set(0)), new SetRanger())
      val bs = new BoundedSum(0, 2)
      assert(bs.revise(rw, Equation(List(Addend(1, 0), Addend(1, 3), Addend(1, 4)), Eq(), 2)))
      assert(rw.changes.isEmpty)
    }

    {
      val rw = new ReadWriteMock[Set[Int], Int](Map(0 -> Set(0), 3 -> Set(0, 1, 2), 4 -> Set(0)), new SetRanger())
      val bs = new BoundedSum(0, 2)
      assert(!bs.revise(rw, Equation(List(Addend(1, 0), Addend(1, 3), Addend(1, 4)), Eq(), 3)))
      assert(rw.changes.isEmpty)
    }

    {
      val rw = new ReadWriteMock[Set[Int], Int](Map(0 -> Set(0), 1 -> Set(0, 1, 2), 2 -> Set(0, 1, 2)), new SetRanger())
      val bs = new BoundedSum(0, 3)
      assert(bs.revise(rw, Equation(List(Addend(1, 0), Addend(1, 1), Addend(1, 2)), Eq(), 4)))
      println(rw.changes)
      assert(rw.changes.equals(Map(1 -> Set(2), 2 -> Set(2))))
    }

    {
      val rw = new ReadWriteMock[Set[Int], Int](Map(0 -> Set(0), 1 -> Set(0, 1, 2, 3), 2 -> Set(0, 1, 2, 3)), new SetRanger())
      val bs = new BoundedSum(0, 3)
      assert(bs.revise(rw, Equation(List(Addend(1, 0), Addend(1, 1), Addend(1, 2)), Eq(), 4)))
      assert(rw.changes.equals(Map(1 -> Set(1, 2, 3), 2 -> Set(1, 2, 3))))
    }

    def assertResolution(eq1: Equation, eq2: Equation, expected: Equation) {
      val bs = new BoundedSum(0, 3)
      val input: List[(Int, Option[MixedConstraint])] = List((0, Some(Right(eq1))), (0, Some(Right(eq2))))
      val learned:  List[(Equation,List[MixedConstraint])] = bs.learn(input)
      println("learned: " + learned)
      val expect: List[(Equation,List[MixedConstraint])] = List((expected, input.map(_._2.get)))
      assert(learned.equals(expect))
    }

    assertResolution(
      Equation(List(Addend(1, 0), Addend(1, 1), Addend(1, 2)), Eq(), 4),
      Equation(List(Addend(1, 0), Addend(1, 3), Addend(1, 4)), Eq(), 7),
      Equation(List(Addend(1, 1), Addend(1, 2), Addend(-1, 3), Addend(-1, 4)), Eq(), -3)
    )

    def assertRelations(rel1: Relation, rel2: Relation, expected: Relation) {
      assertResolution(
        Equation(List(Addend(2, 0), Addend(3, 1)), rel1, 11),
        Equation(List(Addend(-5, 0), Addend(7, 1)), rel2, 13),
        Equation(List(Addend(19, 1)), expected, 81)
      )
    }

    assertRelations(Eq(), Eq(), Eq())
    assertRelations(LtEq(), LtEq(), LtEq())
    assertRelations(GtEq(), GtEq(), GtEq())
    assertRelations(LtEq(), Eq(), LtEq())
    assertRelations(GtEq(), Eq(), GtEq())
    assertRelations(Eq(), LtEq(), LtEq())
    assertRelations(Eq(), GtEq(), GtEq())

    {
      val bs = new BoundedSum(0, 3)
      val eq1 = Equation(List(Addend(1, 0), Addend(1, 1)), LtEq(), 7)
      val eq2 = Equation(List(Addend(1, 0), Addend(2, 1)), GtEq(), 11)
      val input: List[(Int, Option[MixedConstraint])] = List((0, Some(Right(eq1))), (0, Some(Right(eq2))))
      val learned:  List[(Equation,List[MixedConstraint])] = bs.learn(input)
      println("learned: " + learned)
      val expected = Equation(List(Addend(-1, 1)), LtEq(), -4)
      val expect: List[(Equation,List[MixedConstraint])] = List((expected, input.map(_._2.get)))
      assert(learned.equals(expect))
    }

    {
      val bs = new BoundedSum(0, 3)
      val eq1 = Equation(List(Addend(1, 0), Addend(1, 1)), LtEq(), 7)
      val eq2 = Equation(List(Addend(1, 0), Addend(2, 1)), LtEq(), 11)
      val input: List[(Int, Option[MixedConstraint])] = List((0, Some(Right(eq1))), (0, Some(Right(eq2))))
      val learned:  List[(Equation,List[MixedConstraint])] = bs.learn(input)
      println("learned: " + learned)
      val expect: List[(Equation,List[MixedConstraint])] = List() // perhaps we COULD infer something here, but I'm not quite ready to open that can of worms
      assert(learned.equals(expect))
    }

    // definitely should write more of these
  }
}

