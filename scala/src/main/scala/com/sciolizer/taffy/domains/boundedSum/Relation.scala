package com.sciolizer.taffy.domains.boundedSum

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/21/13
 * Time: 5:41 PM
 */
sealed trait Relation {
  def multiply(coefficient: Int): Relation
}

case class Eq() extends Relation { def multiply(_coefficient: Int) = Eq() }
case class LtEq() extends Relation { def multiply(coefficient: Int) = if (coefficient < 0) GtEq() else LtEq() }
case class GtEq() extends Relation { def multiply(coefficient: Int) = if (coefficient < 0) LtEq() else GtEq() }

