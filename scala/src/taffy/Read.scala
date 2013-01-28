package taffy

import collection.mutable

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 10:58 AM
 */
class Read[Variables, Variable](variables: mutable.ArrayBuffer[Variables], ranger: Ranger[Variables, Variable]) {
  def read(vid: Int) : Variable = ranger.fromSingleton(variables(vid))
}
