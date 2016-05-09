import leon.lang._
import leon.annotation._
import leon.proof._
 
object StringTest {
  sealed abstract class Nat
  case class Succ(n: Nat) extends Nat
  case object Zero extends Nat
  
  def fc(n: Nat, a: String, b: String, c: String): String = n match {
    case Succ(n) => a + fc(n, a, b, c) + b
    case Zero => c
  }
  
  def LemmaEquationSplit(A: String, B: String, C: String, D: String) = {
    require(A + B == C + D && A.bigLength == C.bigLength)
    A == C && B == D
  }.holds
  
  def LemmaInequalitySplit(p: String, q: String) = {
    p.bigLength < q.bigLength || p.bigLength == q.bigLength || p.bigLength > q.bigLength
  }.holds
  
  def stripPrefix(s: String, i: BigInt): String = {
    s.bigSubstring(i)
  }
  /*3) prefix-introduce (similar for suffix-introduce)
| p |`< | q |  && p A = q B
<=>
There exist a constant k such that q = p k and A = k B*/
  def LemmaPrefixIntroduce(p: String, q: String, A: String, B: String) = {
    require(p.bigLength < q.bigLength && p + A == q + B)
    val k = stripPrefix(q, p.bigLength)
    k
  } ensuring { (k: String) => q == p + k && A == k + B }
  
  def LemmaCommutation1(A: String, B: String, C: String) = {
    require(A + B == C + A && C.bigLength >= A.bigLength)
    val k2 = stripPrefix(C, A.bigLength)
    val k1 = A
    (k1, k2)
  } ensuring {
    k => C == k._1 + k._2 && B == k._2 + k._1 && A == k._1
  }
  
  def LemmaCommutation2(A: String, B: String, C: String): (String, String) = {
    require(A + B == C + A)
    if(C.bigLength < A.bigLength) {
      val Ap = stripPrefix(A, C.bigLength)
      LemmaCommutation2(Ap, B, C)
    } else {
      LemmaCommutation1(A, B, C)
    }
  } ensuring {
    k => C == k._1 + k._2 && B == k._2 + k._1 // Maybe something on A
  }
  
  def power(A: String, n: BigInt): String = {
    require(n >= 0)
    if(n == 0) ""
    else if(n == 1) A
    else A + power(A, n-1)
  }
  
  def LemmaAssociative(A: String, B: String, C: String): Boolean = {
    (A + B) + C == A + (B + C)
  } holds

  def LemmaCommutative(A: String, B: String, n: BigInt): Boolean = {
    require(A + B == B + A && n >= 0 && n <= 2)
    B + power(A, n) == power(A, n) + B because {
      if(n == 0) trivial
      else if(n == 1) trivial
      else {
        B + power(A, n)         ==| trivial |
        B + (A + power(A, n-1)) ==| LemmaAssociative(B, A, power(A, n-1)) |
        (B + A) + power(A, n-1) ==| trivial |
        (A + B) + power(A, n-1) ==| LemmaAssociative(A, B, power(A, n-1)) |
        A + (B + power(A, n-1)) ==| LemmaCommutative(A, B, n-1) |
        A + (power(A, n-1) + B) ==| LemmaAssociative(A, power(A, n-1), B) |
        (A + power(A, n-1)) + B ==| trivial |
        power(A, n) + B
      } qed
    }
  } holds
  
  /*@induct
  def LemmaCommutative2(A: String, B: String, n: BigInt): Boolean = {
    require(A + B == B + A && n >= 0)
    power(A + B, n) == power(A, n) + power(B, n) because {
      if(n == 0) trivial
      else if(n == 1) trivial
      else {
        power(A, n) == A + power(A, n - 1)
        power(B, n) == B + power(B, n - 1)
        power(A + B, n)
          == A + B + power(A + B, n - 1)
          == A + B + power(A, n - 1) + power(B, n - 1)
          == B + A + power(A, n - 1) + power(B, n - 1)
          == B + power(A, n) + power(B, n - 1)
      }
    }
  } holds*/
/*


4) Constructive commutation
if A B = C A, then there exists k1 and k2 such that C = k1 k2 and B = k2 k1  and
   if |B| + |C|  > |A|  then A = k1 k2 k1
   if |B| + |C|  <= |A|  then A = k1 k2 k1 k2 k1

5) Commutative recurrence
if A B = B A, then (A B)^n = A^n B^n
6) Power Equivalence
 (A B)^n A = A (B A)^n*/
  
  def theorem(n: Nat, A: String, B: String, C: String, D: String, E: String, F: String) = {
    require{
      val f = (n: Nat) => fc(n, A, B, C)
      val g = (n: Nat) => fc(n, D, E, F)
      f(Zero) == g(Zero) &&
      f(Succ(Zero)) == g(Succ(Zero))  &&
      f(Succ(Succ(Zero))) == g(Succ(Succ(Zero)))}
    fc(n, A, B, C) == fc(n, D, E, F) because {
      true
      
      /*f(Zero) == g(Zero) <=> C = F
      1. f(Succ(Zero)) == g(Succ(Zero)) <=> ACB = DCE
      2. f(Succ(Succ(Zero))) == g(Succ(Succ(Zero))) <=> AACBB = DDCEE
      
      suppose n s.t. f(n) != g(n) : n is smallest
      so n = Succ(n'), f(n') = g(n') = X
      
      |A| < |D|  ==> |E| < |B|
      <=> Exists K, M s.t.
      AK = D && B = ME
      
      1. ACME = AKCE
      2. AACMEME = AKAKCEE
      
      1. CM = KC
      2. ACMEM = KAKCE
      
      exists R, S
      K = RS
      M = SR
        Si |C| < |M| + |M|
          C = RSRSRSR  (CSR = RSC)
          2. ARSRSRESR = RSARSRSRE
          <=>
             ARS = RSA
             ESR = SRE
             
             //f(n) = A^n C B^n = A^n RSR (SR E)^n = A^n R(SR)^(n+1) E^n =
             //g(n) = D^n F E^n = (A RS)^n RSR E^n= A^n (RS)^(n+1)R E^n
             
             f(n) = A + f(n') + B != D + g(n') + E
             AXB != DXE
             <=>
             AXME != AKXE
             <=>
             XSR != RSX
             
             si n' = Zero, X = C = RSR
             CSR != RSC
             Donc n' != Zero, n' = Succ(n'')  X = f(n') = AYB = DYE
             
             <=>
             //AYBSR != RSDYE
             
             <=>
             //AYSRESR != RSARSYE
             
             <=>
             AYSR != RSAY
             <=>
             AYSR != ARSY
             <=>
             YSR != RSY
             
             Y != RSR (Y = f(n'')) donc n'' != Zero.
    */}
  }.holds
}