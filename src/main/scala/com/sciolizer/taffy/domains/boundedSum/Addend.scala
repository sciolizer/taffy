package com.sciolizer.taffy.domains.boundedSum

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 2/21/13
 * Time: 5:41 PM
 */
case class Addend(coefficient: Int, variable: Int) {
   def substitute(substitution: Map[Int, Int]): Addend = copy(variable = substitution(variable))
 }
