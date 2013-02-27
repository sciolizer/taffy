package com.sciolizer.taffy.domains.lists

trait ReadsList[+Values] {

  def isEmpty: Values

  def isEmptyBools: Set[Boolean]

  def heads: Option[Values]

  def tails: Option[ReadsList[Values]]

  def snoc: Option[(Values, ReadsList[Values])]

  /** Gives the longest list it can, up to the solver's current search depth. So, for instance, if it returns
    * [Set(1,2),Set(3,4)], then [1, 3] is currently a possible value. [2] is also a possible value, even though
    * it is shorter. [1, 3, 7] is also a possible value, but the solver might not have expanded its search
    * space that far. For this reason, constraints should read from `bounded` as well, to determine if
    * a longer list is still possible.
    *
    * In general, use of isEmpty, heads, and tails should be preferred, to avoid reading more variable values
    * than is necessary to satisfy your constraint. e.g. if you have a constraint which says that the sum of
    * this list should be at least 10 (and all of its numbers are non-negative), you don't want to read all the
    * way to the end of the list.
    *
    * @return Supersequence of many (but not all) possible values for this list at current expansion level
    */
  def values: List[Values]

  /** Whether the list has a bound on its length. Returning false does not indicate that the list
    * must be longer; it only indicates that it CAN be longer.
    *
    * Use of isEmpty and tails is to be preferred, since your constraint might not need to read to the end.
    *
    * @return true only when the list's length is known to be under some value.
    */
  def bounded: Boolean

}
