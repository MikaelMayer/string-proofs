
import leon.lang._
import leon.annotation._
import leon.collection._

/**
  Implementation of the unary yield-deterministic transducer in the paper
  http://ieeexplore.ieee.org/xpls/abs_all.jsp?arnumber=7354436
  
  Equivalence of deterministic top-down tree-to-string transducers is decidable
  by Helmut Seidl, Sebastian Maneth, Gregor Kemper (2015)
*/
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
  
  // We make it total, so there is no option type here.
  val initState = BigInt(1)
  case class UNARY_YDT(nbStates: BigInt, symbols: Set[Symbol], delta: (BigInt, Symbol) => List[UnaryExpr] ) {
    require(nbStates >= 1)
    def evaluate(t: Tree): BigInt = {
      evaluate(t, initState)
    }
    
    // [[t]]q == [[t.symbol (t.children ...) ]]q == [[delta(q, t.symbol)]]_M ([[t.children(0)]]q, ... [[t.children(t.symbol.arity-1)]]q)
    def evaluate(t: Tree, q: BigInt): BigInt = {
      require(q >= 1 && q <= nbStates)
      if(isConsistent(delta(q, t.symbol), t.symbol))
        eval(delta(q, t.symbol), t, 0)
      else BigInt(0)
    }
    
    def isConsistent(u: UnaryExpr, x: Symbol): Boolean = u match {
      case I => true
      case S(s, childIndex) => s >= 1 && s <= nbStates && childIndex >= 1 && childIndex <= x.arity
    }
    
    // Checks if an expression can handle the given symbol.
    def isConsistent(T: List[UnaryExpr], x: Symbol): Boolean = T match {
      case Nil() => true
      case Cons(t, tail) => isConsistent(t, x) && isConsistent(tail, x)
    }
    
    // We can build up consistency
    def LemmaIsConsistent(u: UnaryExpr, T: List[UnaryExpr], x: Symbol): Boolean = {
      require(isConsistent(u, x) && isConsistent(T, x))
      isConsistent(Cons(u, T), x)
    } holds
    
    def LemmaIsConsistent2(T: Cons[UnaryExpr], x: Symbol): Boolean = {
      require(isConsistent(T, x))
      isConsistent(T.tail, x)
    } holds

    // Corresponds to [[T]]_M x
    def eval(T: List[UnaryExpr], x: Tree, acc: BigInt): BigInt = {
      require(isConsistent(T, x.symbol))
      T match {
        case Nil() => acc
        case Cons(I, tail) => eval(tail, x, acc + BigInt(1))
        case Cons(S(childState, childIndex), tail) => 
          val child = x.children(childIndex - 1)
          val unaryExprs = delta(childState, child.symbol)
          val res = if(isConsistent(unaryExprs, child.symbol)) eval(unaryExprs, child, 0) else BigInt(0)
          eval(tail, x, acc + res)
      }
    }
    
    // [[t]] for any state.
    def evaluateForAll(t: Tree): Vector[BigInt] = {
      def recEval(s: BigInt, t: Tree, acc: List[BigInt]): List[BigInt]= {
        require(s >= 0 && s + acc.length == nbStates)
        if(s <= 0) {
          acc
        } else {
          recEval(s - 1, t, evaluate(t, s)::acc)
        }
      } ensuring {
        (res: List[BigInt]) => res.length == s + acc.length
      }
      val l = recEval(nbStates, t, Nil())
      Vector(nbStates, l)
    }
    
    // Used by evaluateForAllUnaryExpr
    def evaluateForAllUnaryExpr2(xi: Vector[BigInt], j: BigInt): BigInt = {
      require(xi.size == nbStates && j >= 1 && j <= nbStates)
      if(xi.size == xi.content.length) {
        xi.content(j - 1)
      } else error[BigInt]("Should not happen")
    }
    
    // [[T]] x
    def evaluateForAllUnaryExpr(f: Symbol, T: List[UnaryExpr], x: Vector[Vector[BigInt]]): BigInt = {
      require(x.size == f.arity && x.content.forall(xi => xi.size == nbStates) && isConsistent(T, f))
      T match {
        case Nil() => BigInt(0)
        case Cons(I, tail) => evaluateForAllUnaryExpr(f, tail, x) + BigInt(1)
        case c@Cons(S(j, i), tail) => 
          if( LemmaIsConsistent2(c, f) && isConsistent(tail, f) &&
              i >= 1 && i <= f.arity && j >= 1 && j <= nbStates &&
              ListSpecs.applyForAll(x.content, i-1, (xi: Vector[BigInt]) => xi.size == nbStates) &&
              x.content(i-1).size == nbStates) {
            val xi: Vector[BigInt] = x.content(i-1)
            val res = evaluateForAllUnaryExpr2(xi, j)
            res + evaluateForAllUnaryExpr(f, tail, x)
          } else error[BigInt]("Should not happen")
      }
    }
  }
}
 