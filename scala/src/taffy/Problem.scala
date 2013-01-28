package taffy

import scala.collection.mutable

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 10:31 AM
 */
class Problem[Constraint, Variable](var numVariables: Int, constraints: mutable.Set[Constraint]) {
  def this(numVariables: Int, constraints: Set[Constraint], isomorphisms: List[List[(Int, Int)]])
    = this(numVariables, mutable.Set(constraints.toSeq:_*))
}
