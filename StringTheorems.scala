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
  
  // Splits the string at a given index.
  def split(s: String, i: BigInt): (String, String) = {
    require(i >= 0 && i <= s.bigLength)
    (s.bigSubstring(0, i), s.bigSubstring(i))
  } ensuring {
    res => res._1 + res._2 == s && res._1.bigLength == i && res._2.bigLength == s.bigLength - i
  }
  
  // Splits the string at a given index starting from the end
  def splitFromEnd(s: String, i: BigInt): (String, String) = {
    require(i >= 0 && i <= s.bigLength)
    val j = s.bigLength - i
    split(s, j)
  } ensuring {
    res => res._1 + res._2 == s && res._1.bigLength == s.bigLength - i && res._2.bigLength == i
  }
  
  // Computes A + A + ... + A,  n times */
  def power(A: String, n: BigInt): String = {
    require(n >= 0)
    if(n == 0) ""
    else if(n == 1) A
    else A + power(A, n-1)
  }
  
  /** A + B == C + D and |A| == |C| <==> B == D && A == C */
  def Lemma001EquationSplit(A: String, B: String, C: String, D: String) = {
    require(A + B == C + D && A.bigLength == C.bigLength)
    A == C && B == D
  }.holds
  
  def Lemma002InequalitySplit(p: String, q: String) = {
    p.bigLength < q.bigLength || p.bigLength == q.bigLength || p.bigLength > q.bigLength
  }.holds
  
  // If a string right-commutes with C to yield B on the left, B and C have the same size.
  def Lemma003Stringsizes(A: String, B: String, C: String) = {
    require(A + B == C + A)
    C.bigLength == B.bigLength
  } holds
  
  
  // Associativity
  def LemmaAssociativity(A: String, B: String, C: String): Boolean = {
    (A + B) + C == A + (B + C)
  } holds
  
  // Left simplification
  def LemmaLeftSimplification(A: String, B: String, C: String): Boolean = {
    require(C + A == C + B)
    A == B
  } holds
  
  // Right simplification
  def LemmaRightSimplification(A: String, B: String, C: String): Boolean = {
    require(A + C == B + C)
    A == B
  } holds
  
  /*3) prefix-introduce
| p |`< | q |  && p A = q B
<=>
There exist a constant k such that q = p k and A = k B*/
  def Lemma005PrefixIntroduce(p: String, q: String, A: String, B: String) = {
    require(p.bigLength < q.bigLength && p + A == q + B)
    val (l, k) = split(q, p.bigLength)
    k
  } ensuring { (k: String) => q == p + k && A == k + B }
  
  /*3bis) suffix-introduce
| p |`< | q |  && A p = B q
<=>
There exist a constant k such that q = k p and A = B k */
  def Lemma006SuffixIntroduce(p: String, q: String, A: String, B: String) = {
    require(p.bigLength < q.bigLength && A + p == B + q)
    val (k, l) = splitFromEnd(q, p.bigLength)
    k
  } ensuring { (k: String) => q == k + p && A == B + k }

/*
If A + B == C + A and |A| <= |C|, then there exists k1 and k2 such that
C = k1+k2
B = k2+k1
A = k1
*/
  def LemmaCommutation1(A: String, B: String, C: String) = {
    require(A + B == C + A && C.bigLength >= A.bigLength)
    val (k1, k2) = split(C, A.bigLength)
    (k1, k2)
  } ensuring {
    k => C == k._1 + k._2 && B == k._2 + k._1 && A == k._1
  }

/*
  If A + B == C + A and |A| <= |C|, then there exists k1 and k2 such that
  C = k1+k2
  B = k2+k1
  A = k1+k2+k1+..+k2+k1

2)    | C |    Ap      |
1)| C |       A        |
1)|       A        | B |
2)    |    Ap      |

  Hence Ap commutes with C and yields B
*/
  def LemmaPreCondCommutation1(A: String, B: String, C: String): Boolean = {
    require(A + B == C + A && C.bigLength < A.bigLength)
    val (cp, ap) = split(A, C.bigLength)
    cp == C &&
    A == C + ap
  } holds
  
  def LemmaPreCondCommutation2(A: String, B: String, C: String): Boolean = {
    require(A + B == C + A && C.bigLength < A.bigLength)
    val (app, bp) = splitFromEnd(A, B.bigLength)
    bp == B &&
    app + bp == A
  } holds
  
  def LemmaPreCondCommutation(A: String, B: String, C: String): Boolean = {
    require(A + B == C + A && C.bigLength < A.bigLength)
    val (cp, ap) = split(A, C.bigLength)
    val (app, bp) = splitFromEnd(A, B.bigLength)
    LemmaPreCondCommutation1(A, B, C) &&
    LemmaPreCondCommutation2(A, B, C) &&
    C + ap == A &&
    (C + ap) + B == C + A &&
    LemmaAssociativity(C, ap, B) &&
    C + (ap + B) == C + A &&
    LemmaLeftSimplification(ap + B, A, C) &&
    ap + B == A &&
    C + ap == ap + B
  } holds

  def LemmaCommutation2(A: String, B: String, C: String): (String, String, String) = {
    require(A + B == C + A)
    if(C.bigLength >= A.bigLength) {
      val (k1, k2) = LemmaCommutation1(A, B, C)
      (k1, k2, A)
    } else {
      val (c, ap) = split(A, C.bigLength)
      if (LemmaPreCondCommutation(A, B, C)) {
        val k = LemmaCommutation2(ap, B, C)
        (k._1, k._2, k._1 + k._2 + k._3) 
      } else (A, B, C) // Dummy, used because assert, assume, require do not work above.
    }
  } ensuring {
    k => C == k._1 + k._2 && B == k._2 + k._1 && A == k._3
  }

  // Other lemmas
  def LemmaCommutative$0(A: String, B: String, n: BigInt): Boolean = {
    require(n >= 2)
    B + power(A, n) == (B + A) + power(A, n-1)
  } holds
  
  def LemmaCommutative$1(A: String, B: String, n: BigInt): Boolean = {
    require(n >= 2 && A + B == B + A)
    (B + A) + power(A, n-1) == (A + B) + power(A, n-1)
  } holds
  
  def LemmaCommutative$2(A: String, B: String, n: BigInt): Boolean = {
    require(n >= 2 && A + B == B + A)
    (A + B) + power(A, n-1) == A + (B + power(A, n-1))
  } holds
  
  def LemmaCommutative$3(A: String, B: String, n: BigInt): Boolean = {
    require(n >= 2 && A + B == B + A)
    A + (power(A, n-1) + B) == (A + power(A, n-1)) + B
  } holds
  
  def LemmaCommutative$4(A: String, B: String, n: BigInt): Boolean = {
    require(n >= 2 && A + B == B + A)
    (A + power(A, n-1)) + B == power(A, n) + B
  } holds
  
  def emptyStringCommutes(A: String): Boolean = {
    A + "" == "" + A
  } holds

  /*def LemmaCommutative(A: String, B: String, n: BigInt): Boolean = {
    require(A + B == B + A && n >= 0)
    B + power(A, n) == power(A, n) + B because {
      if(n == 0) power(A, 0) == "" && emptyStringCommutes(B)
      else if(n == 1) power(A, 1) == A && B + A == A + B
      else {
        B + power(A, n)         ==| LemmaCommutative$0(A,B,n) |
        (B + A) + power(A, n-1) ==| LemmaCommutative$1(A,B,n) |
        (A + B) + power(A, n-1) ==| LemmaCommutative$2(A,B,n) |
        A + (B + power(A, n-1)) ==| LemmaCommutative(A, B, n-1) |
        A + (power(A, n-1) + B) ==| LemmaCommutative$3(A,B,n) |
        (A + power(A, n-1)) + B ==| LemmaCommutative$4(A,B,n) |
        power(A, n) + B
      } qed
    }
  } holds*/
  
  def LemmaCommutative(A: String, B: String, n: BigInt): Boolean = {
    require(A + B == B + A && n >= 0)
    (
      if(n == 0) power(A, 0) == "" && emptyStringCommutes(B)
      else if(n == 1) power(A, 1) == A && B + A == A + B
      else {
         LemmaCommutative$0(A,B,n) &&
         LemmaCommutative$1(A,B,n) &&
         LemmaCommutative$2(A,B,n) && 
         LemmaCommutative(A, B, n-1) &&
         LemmaCommutative$3(A,B,n) &&
         LemmaCommutative$4(A,B,n)
      }
    ) && B + power(A, n) == power(A, n) + B 
  } holds
  
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
