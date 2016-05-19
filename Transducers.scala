
import leon.lang._
import leon.annotation._
import leon.collection._

object YDT {
  case class Tree(symbol: Symbol, children: List[Tree]) {
    require(symbol.arity == children.length)
  }
  
  case class Symbol(name: BigInt, arity: BigInt)
  
  abstract class UnaryExpr
  case object I extends UnaryExpr
  case class S(state: BigInt, childIndex: BigInt) extends UnaryExpr
  
  case class Vector[T](size: BigInt, content: List[T]) {
    require(size >= 1 && content.length == size)
  }
  
  val initState = BigInt(1)
  case class UNARY_YDT(nbStates: BigInt, symbols: Set[Symbol], delta: (BigInt, Symbol) => Option[List[UnaryExpr]] ) {
    require(nbStates >= 1)
    def evaluate(t: Tree): Option[BigInt] = {
      evaluate(t, initState)
    }
    
    // [[t]]q == [[t.symbol (t.children ...) ]]q == [[delta(q, t.symbol)]]_M ([[t.children(0)]]q, ... [[t.children(t.symbol.arity-1)]]q)
    def evaluate(t: Tree, q: BigInt): Option[BigInt] = {
      require(q >= 1 && q <= nbStates)
      delta(q, t.symbol) match {
        case None() => None()
        case Some(unaryExprs) => eval(unaryExprs, t, 0)
      }
    }

    // Corresponds to [[T]]_M x
    def eval(T: List[UnaryExpr], x: Tree, acc: BigInt): Option[BigInt] = T match {
      case Nil() => Some(acc)
      case Cons(I, tail) => eval(tail, x, acc + BigInt(1))
      case Cons(S(childState, childIndex), tail) => 
        if(childIndex < 0 || childIndex >= x.symbol.arity)
          None()
        else {
          val child = x.children(childIndex)
          delta(childState, child.symbol) match {
            case None() => None()
            case Some(unaryExprs) =>
              eval(unaryExprs, child,0) match {
                case None() => None()
                case Some(res) =>
                  eval(tail, x, acc + res)
              }
          }
        }
    }
    
    // [[t]] for any state.
    def evaluateForAll(t: Tree): Vector[Option[BigInt]] = {
      def recEval(s: BigInt, t: Tree, acc: List[Option[BigInt]]): List[Option[BigInt]]= {
        require(s >= 0 && s + acc.length == nbStates)
        if(s <= 0) {
          acc
        } else {
          recEval(s - 1, t, evaluate(t, s)::acc)
        }
      } ensuring {
        (res: List[Option[BigInt]]) => res.length == s + acc.length
      }
      val l = recEval(nbStates, t, Nil())
      Vector(nbStates, l)
    }
  }
}
 