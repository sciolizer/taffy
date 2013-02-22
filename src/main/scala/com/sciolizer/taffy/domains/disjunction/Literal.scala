package com.sciolizer.taffy.domains.disjunction

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/21/13
 * Time: 5:13 PM
 */
case class Literal(expected: Boolean, vid: Int) {
   def substitute(substitution: Map[Int, Int]): Literal = copy(vid = substitution(vid))
 }
