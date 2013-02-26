package com.sciolizer.taffy.domains.boundedSum

import com.sciolizer.taffy._

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/31/13
 * Time: 10:16 AM
 *
 */
class BoundedSum(minimum: Int, maximum: Int /*, ordering: WellOrdered */) extends Inference[Equation] {

  if (minimum < 0) throw new IllegalArgumentException("Negative minimums is not currently supported: " + minimum)
  if (minimum > maximum) throw new IllegalArgumentException("maximum " + maximum + "must be greater than minimum " + minimum)

  def substitute[C <: Equation](constraint: C, substitution: Map[VarId, VarId]): Equation =
    constraint.substitute(substitution)
                                                   /*
  override def learn(constraints: List[(VarId, MixedConstraint)]): List[(Equation, List[MixedConstraint])] = {
    val vars = constraints.map(_._1).toSet
    superSimpleLearn(vars, constraints.map(_._2).toSet)
  }

  override def superSimpleLearn(vars: Set[VarId], constraints: Set[MixedConstraint]): List[(Equation, List[MixedConstraint])] = {
    val cs = (for (Right(eq) <- constraints) yield { eq }).toSet.toArray
//    println("to learn: " + cs.toList)
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
            val sameDirection: Boolean = eq1.relation match {
              case Eq() => true
              case LtEq() => !eq2.relation.equals(GtEq())
              case GtEq() => !eq2.relation.equals(LtEq())
            }
            val sameSigns: Boolean = math.signum(eq1coefficient) == math.signum(eq2coefficient)
            if (sameSigns != sameDirection || (eq1.relation.equals(Eq()) && eq2.relation.equals(Eq()))) {
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
              val newEq2Relation = eq2.relation.multiply(eq1coefficient)
              val rel: Relation = eq1.relation.multiply(-eq2coefficient) match {
                case Eq() => newEq2Relation
                case LtEq() => if (newEq2Relation != GtEq()) LtEq() else throw new RuntimeException("mismatched inequalities")
                case GtEq() => if (newEq2Relation != LtEq()) GtEq() else throw new RuntimeException("mismatched inequalities")
              }
              ret(Equation(addends, rel, eq1.sum * -eq2coefficient + eq2.sum * eq1coefficient)) = List(Right(eq1), Right(eq2))
            } // else resolution is much more complicated, and not something I'm ready to jump into
          }
        }
      }
    }
//    println("learned: " + ret)
    ret.toList
  }           */
}
                               /*
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
      val input: List[(Int, MixedConstraint)] = List((0, Right(eq1)), (0, Right(eq2)))
      val learned:  List[(Equation,List[MixedConstraint])] = bs.learn(input)
      println("learned: " + learned)
      val expect: List[(Equation,List[MixedConstraint])] = List((expected, input.map(_._2)))
      assert(learned.equals(expect))
    }

    assertResolution(
      Equation(List(Addend(1, 0), Addend(1, 1), Addend(1, 2)), Eq(), 4),
      Equation(List(Addend(1, 0), Addend(1, 3), Addend(1, 4)), Eq(), 7),
      Equation(List(Addend(1, 3), Addend(-1, 1), Addend(1, 4), Addend(-1, 2)), Eq(), 3)
    )

    assertResolution(
      Equation(List(Addend(1, 3), Addend(-1, 0)), Eq(), 0),
      Equation(List(Addend(1, 4), Addend(1, 0)), LtEq(), 1),
      Equation(List(Addend(-1, 3), Addend(-1, 4)), GtEq(), -1)
    )

    def assertRelations(rel1: Relation, rel2: Relation, expected: Relation) {
      assertResolution(
        Equation(List(Addend(2, 0), Addend(3, 1)), rel1, 11),
        Equation(List(Addend(-5, 0), Addend(7, 1)), rel2, 13),
        Equation(List(Addend(29, 1)), expected, 81)
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
      val input: List[(Int, MixedConstraint)] = List((0, Right(eq1)), (0, Right(eq2)))
      val learned:  List[(Equation,List[MixedConstraint])] = bs.learn(input)
//      println("learned: " + learned)
      val expected = Equation(List(Addend(1, 1)), GtEq(), 4)
      val expect: List[(Equation,List[MixedConstraint])] = List((expected, input.map(_._2)))
      assert(learned.equals(expect))
    }

    {
      val bs = new BoundedSum(0, 3)
      val eq1 = Equation(List(Addend(1, 0), Addend(1, 1)), LtEq(), 7)
      val eq2 = Equation(List(Addend(1, 0), Addend(2, 1)), LtEq(), 11)
      val input: List[(Int, MixedConstraint)] = List((0, Right(eq1)), (0, Right(eq2)))
      val learned:  List[(Equation,List[MixedConstraint])] = bs.learn(input)
//      println("learned: " + learned)
      val expect: List[(Equation,List[MixedConstraint])] = List() // perhaps we COULD infer something here, but I'm not quite ready to open that can of worms
      assert(learned.equals(expect))
    }

    // definitely should write more of these
  }
}

*/