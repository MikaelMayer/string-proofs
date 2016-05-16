import leon.lang._
import leon.annotation._
import leon.collection._
import leon.lang.synthesis._
import leon.proof._

object DovJardenTheorem {
  
  /** Hierarchy of classes of expressions */
  abstract class Expr
  
  /** A single number */
  case class Number(r: BigInt) extends Expr
  
  /** The square root of an expression */
  case class Sqrt(r: Expr) extends Expr
  
  /** An expression to the power of another expression */
  case class Power(a: Expr, n: Expr) extends Expr
  
  /** An expressions times another expression */
  case class Times(a: Expr, n: Expr) extends Expr
  
  
  // Sample numbers
  val two = Number(BigInt(2))
  val sqrt2 = Sqrt(two)
  
  // The evaluation function or maximum simplification
  def eval(e: Expr): Expr = (e match {
    case e: Number => e
    case Sqrt(e) => eval(e) match {
      case Number(BigInt(4)) => Number(BigInt(2))
      case f => Sqrt(f)
    }
    case Times(n, m) => (eval(n), eval(m)) match {
      case (Sqrt(a), Sqrt(b)) => eval(Sqrt(Times(a, b)))
      case (Number(a), Number(b)) => Number(a * b)
      case (a, b) => Times(a, b)
    }
    case Power(a, b) => (eval(a), eval(b)) match {
      case (Sqrt(n), Number(BigInt(2))) => n
      case (Power(a, n), m)                   => eval(Power(a, Times(n, m)))
      case (a, b)                             => Power(a, b)
    }
  }) ensuring {
    (res: Expr) => (e, res) passes {
      case x if x == Times(sqrt2, sqrt2) => Number(BigInt(2))
    }
  }

  // The non-constructive theorem
  def findTwoIrrationalsWhosePowerIsRational(isRat: Expr => Boolean): (Expr, Expr) = {
    require(isRat(two) && !isRat(sqrt2))
    if(isRat(Power(sqrt2, sqrt2))) {
      (sqrt2, sqrt2)
    } else {
      (Power(sqrt2, sqrt2), sqrt2)
    }
  } ensuring {
    (res: (Expr, Expr) ) =>
      !isRat(res._1) && !isRat(res._2) &&
      isRat(eval(Power(res._1, res._2)))
  }
}
