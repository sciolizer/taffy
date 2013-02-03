package taffy

/**
 * Created with IntelliJ IDEA.
 * User: jball
 * Date: 1/28/13
 * Time: 4:27 PM
 */
class NoGood[Variables](val forbidden: Map[Int, Variables]) {
  def coverage(): Set[Int] = forbidden.keySet

  def revise[Constraint, Variable](rw: ReadWrite[Variables, Variable], ranger: Ranger[Variables, Variable]): Boolean = {
    getUnit(rw, ranger) match {
      case Left(b) => b
      case Right((vid, diff)) => rw.intersectVar(vid, diff); true
    }
  }

  def isUnit[Constraint, Variable](rw: ReadWrite[Variables, Variable], ranger: Ranger[Variables, Variable]): Boolean = {
    getUnit(rw, ranger) match {
      case Left(_) => false
      case Right(_) => true
    }
  }

  private def getUnit[Constraint, Variable](rw: ReadWrite[Variables, Variable], ranger: Ranger[Variables, Variable]): Either[Boolean, (Int, Variables)] = {
    var accepts: Option[(Int, Variables)] = None
    for ((vid, values1) <- forbidden) {
      val values2: Variables = rw.readVar(vid)
      val intersection: Variables = ranger.intersection(values1, values2)
      if (ranger.isEmpty(intersection)) {
        // The clause is true, and we can't make a deduction
        return Left(true)
      } else {
        val diff: Variables = ranger.subtraction(values2, values1)
        if (!ranger.isEmpty(diff)) {
          // This portion of the clause is true.
          accepts match {
            case None => accepts = Some((vid, diff)) // remember this var, in case we are the only portion of the clause that can be true
            case Some(_) => return Left(true) // At least two portions of this clause are true, so we can't make any deductions.
          }
        }
      }
    }
    accepts match {
      case None => Left(false) // each portion of the clause was false
      case Some((vid, diff)) => Right((vid, diff)) // Only one portion of the clause is true, and we can make a deduction!
    }
  }

  override def toString: String = {
    forbidden.toString()
  }
}
