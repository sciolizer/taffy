package com.sciolizer.taffy

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 10:31 AM
 */
class Problem[Constraint, Values, Value](
  val numVariables: Int,
  val constraints: Set[Constraint],
  val candidateValues: Values,
  val isomorphisms: Isomorphisms = NoIsomorphisms) {
}
