package com.sciolizer.taffy

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 10:58 AM
 */
class Read[Constraint, Variables, Variable](graph: ImplicationGraph[Constraint, Variables, Variable], ranger: Ranger[Variables, Variable]) {
  def read(vid: Int) : Variable = ranger.fromSingleton(graph.readVar(vid))
}
