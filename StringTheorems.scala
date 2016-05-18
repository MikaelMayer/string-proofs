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
  
  // Useful bigger associativity lemma
  def LemmaAssociativity4(A: String, B: String, C: String, D: String): Boolean = {
    A + (B + C + D) == ((A + B) + C) + D
  } holds
  
  // Useful bigger associativity lemma
  def LemmaAssociativity5_1_2(A: String, B: String, C: String, D: String, E: String): Boolean = {
    A + (B + C + D + E) == (A + B) + (C + D + E)
  } holds
  
  // Left simplification
  def LemmaLeftSimplification(A: String, B: String, C: String): Boolean = {
    require(A + B == A + C)
    B == C
  } holds
  
  // Right simplification
  def LemmaRightSimplification(A: String, B: String, C: String): Boolean = {
    require(A + C == B + C)
    A == B
  } holds
  
  
  // Left size simplification
  def LemmaLeftSizeSimplification(A: String, B: String, C: String, D: String): Boolean = {
    require(A.bigLength == C.bigLength && A+B==C+D)
    A == C && B == D
  } holds
  
  // Right size simplification A+B == C+D && |B| == |D| ==> B == D && A == C
  def LemmaRightSizeSimplification(A: String, B: String, C: String, D: String): Boolean = {
    require(B.bigLength == D.bigLength && A+B==C+D)
    A == C && B == D
  } holds
  
  /** |A+B| == |A|+|B|*/
  def LemmaLength(A: String, B: String): Boolean = {
    (A + B).bigLength == A.bigLength + B.bigLength
  } holds
  
  /** Power can also be defined on the right */
  def LemmaPowerRight(A: String, n: BigInt): Boolean = {
    require(n > 0)
    (if(n == 1) power(A, n - 1) == "" && "" + A == A
    else {
      LemmaPowerKeepsCommutativity(A, A, n-1) &&
      power(A, n - 1) + A == A + power(A, n - 1) &&
      A + power(A, n - 1) == power(A, n)
    }) &&
    power(A, n - 1) + A == power(A, n)
  } holds
  
  /*3) prefix-introduce
| p |`< | q |  && p A = q B
<=>
There exist a constant k such that q = p k and A = k B*/
  def Lemma005PrefixIntroduce(p: String, A: String, q: String, B: String) = {
    require(p.bigLength < q.bigLength && p + A == q + B)
    val (l, k) = split(q, p.bigLength)
    k
  } ensuring { (k: String) => q == p + k && A == k + B }
  
  /*3bis) suffix-introduce
| p |`< | q |  && A p = B q
<=>
There exist a constant k such that q = k p and A = B k */
  def Lemma006SuffixIntroduce(A: String, p: String, B: String, q: String) = {
    require(p.bigLength < q.bigLength && A + p == B + q)
    val (k, l) = splitFromEnd(q, p.bigLength)
    k
  } ensuring { (k: String) => q == k + p && A == B + k }

/** If A + B == C + D && |B| < |D| ==> |A| > |C| */
  def LemmaRightGreaterSmaller(A: String, B: String, C: String, D: String) = {
    require(A + B == C + D && B.bigLength < D.bigLength)
    A.bigLength > C.bigLength 
  } holds
  
  /** A + B == B + A ==> there exists t, n, m such that B = nT, A=mT*/
  def LemmaGCD(A: String, B: String): (String, BigInt, BigInt) = {
    require(A + B == B + A)
    if(A.bigLength == B.bigLength) {
      if(LemmaLeftSizeSimplification(A, B, B, A) && A == B) {
        (A, BigInt(1), BigInt(1))
      } else error[(String, BigInt, BigInt)]("This should not happen")
    } else if(A.bigLength < B.bigLength) {
      val (t, na, nb) = LemmaGCD(B, A)
      (t, nb, na)
    } else {
      val k = Lemma005PrefixIntroduce(B, A, A, B)
      if(A == B + k && A == k + B) {
        val (t, nb, nk) = LemmaGCD(B, k)
        (t, nb+nk, nb)
      } else error[(String, BigInt, BigInt)]("This should not happen")
    }
  } ensuring { r => r._2 >= 0 && r._3 >= 0 && A == power(r._1, r._2) && B == power(r._1, r._3) }

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
    LemmaLeftSimplification(C, ap + B, A) &&
    ap + B == A &&
    C + ap == ap + B
  } holds

  /** A + B == C + A ==> C == k1k2 && B == k2k1 */
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
  
  /** A + B == C + A && |C| < |A| ==> C == k1k2 && B == k2k1 && A==k1k2k3 && A == k3k2k1 */
  def LemmaCommutation3(A: String, B: String, C: String): (String, String, String) = {
    require(A + B == C + A && C.bigLength < A.bigLength)
    val (c, ap) = split(A, C.bigLength)
    if (LemmaPreCondCommutation(A, B, C) && c == C && C+ap == A && ap+B == A) {
      val k = LemmaCommutation2(ap, B, C)
      if(k._3 == ap &&
         C == k._1 + k._2 &&
         B == k._2 + k._1 &&
         A == (k._1 + k._2)+k._3 &&
         A == ap + B &&
         A == k._3+(k._2+k._1) && LemmaAssociativity(k._3, k._2, k._1) &&
         A == (k._3+k._2)+k._1
         ) {
        (k._1, k._2, k._3)
      } else error[(String, String, String)]("should not happen")
    } else error[(String, String, String)]("should not happen")
  } ensuring {
    k => C == k._1 + k._2 && B == k._2 + k._1 && A == k._1 + k._2 + k._3 && A == k._3 + (k._2 + k._1) && LemmaAssociativity(k._3, k._2, k._1) && A == k._3 + k._2 + k._1
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
  
  def LemmaRightEquality(A: String, B: String, C: String): Boolean = {
    require(B == C)
    A+B == A+C
  } holds
  
  def LemmaLeftEquality(A: String, B: String, C: String): Boolean = {
    require(A == B)
    A+C == B+C
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
  
  // B + nA == nA + B
  def LemmaPowerKeepsCommutativity(A: String, B: String, n: BigInt): Boolean = {
    require(A + B == B + A && n >= 0)
    (
      if(n == 0) power(A, 0) == "" && emptyStringCommutes(B)
      else if(n == 1) power(A, 1) == A && B + A == A + B
      else {
         LemmaCommutative$0(A,B,n) &&
         LemmaCommutative$1(A,B,n) &&
         LemmaCommutative$2(A,B,n) && 
         LemmaPowerKeepsCommutativity(A, B, n-1) &&
         LemmaCommutative$3(A,B,n) &&
         LemmaCommutative$4(A,B,n)
      }
    ) && B + power(A, n) == power(A, n) + B 
  } holds
  
  // n(A+B) = nA + nB
  def LemmaDblPowerKeepsCommutativity(A: String, B: String, n: BigInt): Boolean = {
    require(A + B == B + A && n >= 0)
    if(n == 0) power(A, 0) == "" && power(B, 0) == ""    && power(A + B, n) == power(A, n) + power(B, n)
    else if(n == 1) power(A, 1) == A && power(B, 1) == B && power(A + B, n) == power(A, n) + power(B, n)
    else {
      power(A + B, n) == (A + B) + power(A + B, n - 1) &&
      LemmaDblPowerKeepsCommutativity(A, B, n-1) &&
       (A + B) + power(A + B, n - 1) == (A + B) + (power(A, n-1) + power(B, n-1)) &&
       LemmaAssociativity(A, B, power(A, n-1) + power(B, n-1)) &&
       (A + B) + (power(A, n-1) + power(B, n-1)) == A + (B + (power(A, n-1) + power(B, n-1))) &&
       LemmaAssociativity(B, power(A, n-1), power(B, n-1)) &&
       A + (B + (power(A, n-1) + power(B, n-1))) == A + ((B + power(A, n-1)) + power(B, n-1)) &&
       LemmaPowerKeepsCommutativity(A, B, n - 1) &&
       //B + power(A, n-1) == power(A, n-1) + B && 
       A + ((B + power(A, n-1)) + power(B, n-1)) == A + ((power(A, n-1) + B) + power(B, n-1)) &&
       LemmaAssociativity(power(A, n-1), B, power(B, n-1)) &&
       A + ((power(A, n-1) + B) + power(B, n-1)) == A + (power(A, n-1) + (B + power(B, n-1))) &&
       LemmaAssociativity(A, power(A, n-1), (B + power(B, n-1))) &&
       A + (power(A, n-1) + (B + power(B, n-1))) == (A + power(A, n-1)) + (B + power(B, n-1)) &&
      (A + power(A, n-1)) + (B + power(B, n-1)) == power(A, n) + power(B, n)
    } &&
    power(A + B, n) == power(A, n) + power(B, n)
  } holds
  
  // A + n(B+A) == n(A+B) + A
  def LemmaPowerEquivalence(A: String, B: String, n: BigInt): Boolean = {
    require(n >= 0)
    if(n == 0)      power(B + A, n) == "" && emptyStringCommutes(A)  && A + power(B + A, n) == power(A + B, n) + A
    else if(n == 1) power(B + A, 1) == B + A && LemmaAssociativity(A, B, A) && A + power(B + A, n) == power(A + B, n) + A
    else {
      A + power(B + A, n) == A + ((B + A) + power(B + A, n - 1)) &&
      LemmaAssociativity(B, A, power(B + A, n - 1)) &&
      A + ((B + A) + power(B + A, n - 1)) == A + (B + (A + power(B + A, n - 1))) &&
      LemmaPowerEquivalence(A, B, n-1) &&
      A + (B + (A + power(B + A, n - 1))) == A + (B + (power(A + B, n - 1) + A)) &&
      LemmaAssociativity(B, power(A + B, n - 1), A) &&
      A + (B + (power(A + B, n - 1) + A)) == A + ((B + power(A + B, n - 1)) + A) &&
      LemmaPowerEquivalence(B, A, n-1) &&
      A + ((B + power(A + B, n - 1)) + A) == A + ((power(B + A, n - 1) + B) + A) &&
      LemmaAssociativity4(A, power(B + A, n - 1), B, A) &&
      A + ((power(B + A, n - 1) + B) + A) == ((A + power(B + A, n - 1)) + B) + A &&
      LemmaPowerEquivalence(A, B, n-1) &&
      ((A + power(B + A, n - 1)) + B) + A == ((power(A + B, n - 1) + A) + B) + A &&
      LemmaAssociativity(power(A + B, n - 1), A, B) &&
      ((power(A + B, n - 1) + A) + B) + A ==  (power(A + B, n - 1) + (A + B)) + A &&
      LemmaPowerRight(A + B, n) &&
      (power(A + B, n - 1) + (A + B)) + A ==  power(A + B, n) + A
    } &&
    A + power(B + A, n) == power(A + B, n) + A
  } holds
  
  def canonicalForm(A: String, r: String, s: String, t: String, E: String) = {
    require( ((A+((r+s)+t))+((s+r)+E))+(s+r) == (r+s)+(((A+(r+s))+(t+(s+r)))+E) && t+(s+r) == (r+s)+t)
    ((A+(r+s))+(t+(s+r)))+(E+(s+r)) == (((r+s)+A)+((r+s)+t))+((s+r)+E) &&
    (E+(s+r)).bigLength == ((s+r)+E).bigLength &&
    LemmaRightSizeSimplification((A+(r+s))+(t+(s+r)), E+(s+r), ((r+s)+A)+((r+s)+t), (s+r)+E) &&
    E+(s+r) == (s+r)+E &&
    (A+(r+s))+(t+(s+r)) == ((r+s)+A)+((r+s)+t) &&
    LemmaLeftSizeSimplification(A+(r+s), t+(s+r), (r+s)+A, (r+s)+t)  &&
    A+(r+s) == (r+s)+A
  } holds
  
  def LemmaExpansion(A: String, B: String, f1: String, f2: String, f3: String): Boolean = {
    require(f2 == A+f1+B && f3 == A+f2+B)
    f3 == A+(A+f1+B)+B
  } holds
  
  def canonically(A: String, fnp: String, s: String, r: String, E: String) = {
    require((r+s)+fnp == fnp+(s+r))
     (A+((r+s)+fnp))+E == (A+(fnp+(s+r)))+E
  } holds
  
  def augmentedTheorem(A1f: String, A1g: String, B1f: String, B1g: String, A0f: String, A0g: String, B0f: String, B0g: String,
      r1: String, s1: String, t1: String, r0: String, s0: String, t0: String, Ef: String, Eg: String, fn: String, gn: String
  ) = {
    require(A1f+(r1+s1) == (r1+s1)+A1f &&
            Ef == t1 + (s1 + r1) &&
            Ef == (r1+s1) + t1 &&
            A1g == A1f+(r1+s1) &&
            B1f ==(s1+r1) + B1g &&
            B1f + (s1+r1) == (s1+r1)+B1f &&
            A0f+(r0+s0) == (r0+s0)+A0f &&
            Eg == t0 + (s0 + r0) &&
            Eg == (r0+s0) + t0 &&
            A0g == A0f+(r0+s0) &&
            B0f ==(s0+r0) + B0g &&
            B0f + (s0+r0) == (s0+r0)+B0f &&
            Ef == Eg &&
            fn == gn &&
            fn+(s1+r1) == (r1+s1)+fn &&
            fn+(s0+r0) == (r0+s0)+fn)
    (A1f+fn+B1f)+(s1+r1) == (r1+s1)+(A1f+fn+B1f)
  } holds

  def reduceForm(n: Nat, np: Nat, A: String, B: String, C: String, D: String, E: String, F: String, s: String, r: String, t: String) = {
    require{
      val f = (n: Nat) => fc(n, A, B, C)
      val g = (n: Nat) => fc(n, D, E, F)
      E+(s+r) == (s+r)+E &&
      A+(r+s) == (r+s)+A &&
      C == F &&
      C == t + (s + r) &&
      D == A + (r + s) &&
      B == (s + r) + E &&
      n == Succ(np) &&
      f(np) == g(np) &&
      f(np)+(s+r) == (r+s)+f(np)
    }
    val f = (n: Nat) => fc(n, A, B, C)
    val g = (n: Nat) => fc(n, D, E, F)
      (f(n) == A+f(np)+B &&
      f(n) == (A+f(np)+(s + r))+E &&
      f(n) == (A+(f(np)+(s+r)))+E &&
      g(n) == D+g(np)+E &&
      g(n) == D+f(np)+E &&
      g(n) == (A+(r+s))+f(np)+E &&
      g(n) == (A+((r+s)+f(np)))+E && canonically(A, f(np), s, r, E) &&
      g(n) == (A+(f(np)+(s+r)))+E) &&
    f(n) == g(n) &&
      (B+(s+r) == ((s+r)+E)+(s+r) &&
      LemmaAssociativity(s+r,E,s+r) &&
      ((s+r)+E)+(s+r) == (s+r)+(E+(s+r)) && E+(s+r) == (s+r)+E &&
      LemmaRightEquality(s+r,E+(s+r),(s+r)+E) &&
      (s+r)+(E+(s+r)) == (s+r)+((s+r)+E) &&
      (s+r)+((s+r)+E) == (s+r)+B) &&
    B+(s+r) == (s+r)+B &&
      (LemmaLeftEquality(f(n),A+f(np)+B, s+r) &&
       f(n) + (s+r) == ((A+f(np))+B) + (s+r) &&
      LemmaAssociativity(A+f(np), B, s+r) &&
      (A+f(np)+B) + (s+r) ==  A+f(np)+(B + (s+r)) && B+(s+r) == (s+r)+B &&
      LemmaRightEquality(A+f(np), B+(s+r), (s+r)+B) &&
      A+f(np)+(B + (s+r)) ==  A+f(np)+((s+r)+B) &&
      LemmaAssociativity(A+f(np), s+r, B) &&
      A+f(np)+((s+r)+B) == (A+f(np)+(s+r))+B &&
      LemmaAssociativity(A, f(np), s+r) &&
      (A+f(np)+(s+r))+B  ==  (A+(f(np)+(s+r)))+B && f(np)+(s+r) == (r+s)+f(np) &&
      LemmaRightEquality(A, f(np)+(s+r), (r+s)+f(np)) &&
      A+(f(np)+(s+r)) == A+((r+s)+f(np)) &&
      LemmaLeftEquality(A+(f(np)+(s+r)), A+((r+s) + f(np)), B) &&
      (A+(f(np)+(s+r)))+B == (A+((r+s) + f(np)))+B &&
      LemmaAssociativity(A, r+s, f(np)) &&
      (A+((r+s)+f(np)))+B == ((A+(r+s))+f(np))+B &&
      ((A+(r+s))+f(np))+B == (((r+s)+A)+f(np))+B &&
      LemmaAssociativity(r+s, A, f(np)) &&
      (((r+s)+A)+f(np))+B == ((r+s)+(A+f(np)))+B &&
      LemmaAssociativity(r+s, A+f(np),B) &&
      ((r+s)+(A+f(np)))+B == (r+s)+(A+f(np)+B) && f(n) == A+f(np)+B &&
      LemmaRightEquality(r+s, f(n), A+f(np)+B) &&
      (r+s)+(A+f(np)+B) == (r+s)+f(n)) &&
    f(n) +(s+r) == (r+s) + f(n)
  } holds
  
  def reduceForm2(A: String, B: String, C: String, D: String, E: String, s: String, r: String, t: String, m: String, k: String) = {
    require(A+(A+C+B)+B == D+(D+C+E)+E &&
      k == r + s &&
      m == s + r &&
      C == r + s + t && C == t + (s + r) &&
      D == A + k &&
      B == m + E
    )
    (A+(A+C+(m + E)))+(m + E) == (D+(D+C+E))+E &&
    LemmaAssociativity(A+(A+C+(m + E)), m, E) &&
    ((A+(A+C+(m + E)))+m) + E == (D+(D+C+E))+E &&
    LemmaRightSimplification((A+(A+C+(m + E)))+m, D+(D+C+E), E) &&
    (A+(A+C+(m + E)))+m == D+(D+C+E) &&
    (A+(A+C+(m + E)))+m == (A+k)+(A+k+C+E) &&
    LemmaAssociativity(A, A+C+(m + E), m) && LemmaAssociativity(A, k, A+k+C+E) &&
    A+((A+C+(m + E))+m) == A+(k+(A+k+C+E)) &&
    LemmaLeftSimplification(A, ((A+C+(m + E))+m), (k+(A+k+C+E))) &&
    A+C+(m+E)+m == k+(A+k+C+E) &&
    A+(r+s+t)+(m+E)+m == k+(A+k+C+E) && C == t+(s+r) &&
    A+(r+s+t)+(m+E)+m == k+(A+k+(t+(s+r))+E) && m == s+r &&
    A+(r+s+t)+((s+r)+E)+(s+r) == k+(A+k+(t+(s+r))+E) && k == r+s &&
    A+(r+s+t)+((s+r)+E)+(s+r) == (r+s)+(A+k+(t+(s+r))+E) && 
    (A+((r+s)+t))+((s+r)+E)+(s+r) == (r+s)+(A+(r+s)+(t+(s+r))+E)
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
 
  def minus1(n: Nat) = {
    require(n.isInstanceOf[Succ])
    n match { case Succ(np) => np }
  } ensuring {
    res => n == Succ(res)
  }
  
  /*@library
  def dummyTheorem(n: Nat, A: String, B: String, C: String, D: String, E: String, F: String) = {
    require{
      val f = (n: Nat) => fc(n, A, B, C)
      val g = (n: Nat) => fc(n, D, E, F)
      f(Zero) == g(Zero) &&
      f(Succ(Zero)) == g(Succ(Zero))  &&
      f(Succ(Succ(Zero))) == g(Succ(Succ(Zero)))}
    val f = (n: Nat) => fc(n, A, B, C)
    val g = (n: Nat) => fc(n, D, E, F)
    f(n) == g(n)
  } holds*/
  
  def theorem(n: Nat, A: String, B: String, C: String, D: String, E: String, F: String) = {
    require{
      val f = (n: Nat) => fc(n, A, B, C)
      val g = (n: Nat) => fc(n, D, E, F)
      f(Zero) == g(Zero) &&
      f(Succ(Zero)) == g(Succ(Zero))  &&
      f(Succ(Succ(Zero))) == g(Succ(Succ(Zero)))}
    val f = (n: Nat) => fc(n, A, B, C)
    val g = (n: Nat) => fc(n, D, E, F)
    f(Zero) == C &&
    g(Zero) == F &&
    C == F &&
    f(Succ(Zero)) == A+C+B &&
    g(Succ(Zero)) == D+F+E &&
    A+C+B == D+C+E &&
    f(Succ(Succ(Zero))) == A+(A+C+B)+B &&
    g(Succ(Succ(Zero))) == D+(D+F+E)+E &&
    A+(A+C+B)+B == D+(D+C+E)+E &&
    (if(E.bigLength == B.bigLength) {
      true
      /*                                          (A+C)+B == (D+C)+E &&
      LemmaRightSizeSimplification(A+C,B,D+C,E)  &&     B == E &&
      LemmaRightSimplification(A+C,D+C,B) &&          A+C == D+C  &&
      LemmaRightSimplification(A,D,C) &&                A == D &&
                                                     f(n) == g(n)*/
    } else (n match {
      case Zero => f(n) == g(n)
      case Succ(Zero) => f(n) == g(n)
      case Succ(np) => 
        if(E.bigLength < B.bigLength) {
          val m = Lemma006SuffixIntroduce(D+C, E, A+C, B)
          B == m + E && D+C == (A+C) + m &&    // ACB = DCE <=> ACm = DC
          LemmaRightGreaterSmaller(D+C, E, A+C, B) &&
          (D+C).bigLength > (A+C).bigLength &&
          LemmaLength(D, C) && LemmaLength(A, C) &&
          D.bigLength + C.bigLength > A.bigLength + C.bigLength &&
          D.bigLength > A.bigLength &&
          LemmaAssociativity(A, C, m) &&
          D+C == A+(C+m) && {
            val k = Lemma005PrefixIntroduce(A, C+m, D, C)
            D == A+k &&                    // ACm = DC <=> Cm = kC
            (A+k)+C == (A+C)+m &&
            LemmaAssociativity(A, k, C) && LemmaAssociativity(A, C, m) &&
            A+(k+C) == A+(C+m) &&
            LemmaLeftSimplification(A, k+C, C+m) &&
            C+m == k+C && (
              if(C.bigLength > k.bigLength) {
                val (r, s, t) = LemmaCommutation3(C, m, k)
                k == r + s &&
                m == s + r &&
                C == r + s + t && C == t + (s + r) &&
                D == A + k &&
                B == m + E &&
                reduceForm2(A, B, C, D, E, s, r, t, m, k) &&
                canonicalForm(A, r, s, t, E) &&
                E+(s+r) == (s+r)+E &&
                A+(r+s) == (r+s)+A &&
                D == A + (r + s) &&
                B == (s + r) + E &&
                n == Succ(np)/* &&
                f(np) == g(np) &&
                f(np)+(s+r) == (r+s)+f(np)
                reduceForm(n, np, A, B, C, D, E, F, s, r, t)*/ // Needs induction hypothesis.
              //f(n) == g(n)
  
              } else {
                val (r, s) = LemmaCommutation1(C, m, k)
                k == r + s &&
                m == s + r &&
                true
              }
            )
          }
        } else {
            E.bigLength > B.bigLength
        }
      })
    )
        
        /* &&
        (A+C).bigLength > (D+C).bigLength &&
        (A+C)+(k+E) == (D+C)+E &&
        LemmaAssociativity(A=C,k,E) &&
        ((A+C)+k)+E == (D+C)+E &&
        LemmaRightSimplification((A+C)+k, D+C, E) &&
        (A+C)+k == D+C &&*/
        
        /* &&
        A.bigLength < D.bigLength*/
      /*val np = minus1(n) // n == Succ(np)
      dummyTheorem(np, A, B, C, D, E, F) &&
      f(np) == g(np) &&
      f(n) == A+f(np)+B &&
      g(n) == D+g(np)+E &&
      A+f(np)+B == D+g(np)+E &&
      n == Succ(np)*/
  }.holds
    /* &&
    g(Succ(Succ(Zero))) == D+g(Succ(Zero))+E *//* &&
    A+A+C+B+B == D+D+F+E+E*/
    /**
    A+A+C+B+B == D+D+F+E+E*/
    //fc(n, A, B, C) == fc(n, D, E, F) because {
    //  true
      
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
    *///}

}
