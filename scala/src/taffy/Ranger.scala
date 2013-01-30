package taffy

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 11:12 AM
 */
trait Ranger[Values, Value] {
  // value returned should guarantee that
  //   values - value does not raise an error
  def pick(values: Values) : Value

  def toSingleton(value: Value) : Values

  /**
   * Inverse of toSingleton. If the collection is not a singleton,
   * an error is raised. Caller is expected to know that the
   * given collection is a singleton. (e.g. after a constraint problem
   * has been successfully solved, every variable should have a singleton
   * of values.)
   * @param values A collection expected to be a singleton.
   * @return The single value in the given collection.
   */
  def fromSingleton(values: Values) : Value

  def isSingleton(values: Values) : Boolean
  def intersection(left: Values, right: Values) : Values
  def subtraction(minuend: Values, subtrahend: Values): Values
  def isEmpty(values: Values) : Boolean
}

class SetRanger[Variable] extends Ranger[Set[Variable], Variable] {
  def toSingleton(value: Variable): Set[Variable] = Set(value)

  /**
   * Inverse of toSingleton. If the collection is not a singleton,
   * an error is raised. Caller is expected to know that the
   * given collection is a singleton. (e.g. after a constraint problem
   * has been successfully solved, every variable should have a singleton
   * of values.)
   * @param values A collection expected to be a singleton.
   * @return The single value in the given collection.
   */
  def fromSingleton(values: Set[Variable]): Variable = if (values.size == 1) values.head else throw new RuntimeException("Values is not a singleton")

  def isSingleton(values: Set[Variable]): Boolean = values.size == 1

  def intersection(left: Set[Variable], right: Set[Variable]): Set[Variable] = left.intersect(right)

  def subtraction(minuend: Set[Variable], subtrahend: Set[Variable]): Set[Variable] = minuend -- subtrahend

  def isEmpty(values: Set[Variable]): Boolean = values.isEmpty

  def pick(values: Set[Variable]): Variable = values.head
}
