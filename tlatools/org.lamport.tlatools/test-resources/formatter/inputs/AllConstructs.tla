---- MODULE AllConstructs ----
(***************************************************************************)
(* A kitchen-sink TLA+ module: operators, quantifiers, CASE, IF/THEN/ELSE, *)
(* CHOOSE, LET/IN, records, functions, sequences, EXCEPT, @, priming,      *)
(* temporal operators, fairness, ENABLED, INSTANCE, RECURSIVE, etc.        *)
(***************************************************************************)

EXTENDS Naturals, Integers, Reals, Sequences, FiniteSets, TLC

(****************************************************************)
(* Parameters and basic assumptions                             *)
(****************************************************************)
CONSTANTS N, S, T, C

ASSUME
  /\ N \in Nat
  /\ S # {}
  /\ S \subseteq T

(****************************************************************)
(* State variables                                              *)
(****************************************************************)
VARIABLES x, y, z, f, r, s, q

vars == << x, y, z, f, r, s, q >>

(****************************************************************)
(* Operator definitions                                         *)
(****************************************************************)

Zero == 0

Add(a, b) == a + b

Equal(a, b) == a = b

RECURSIVE Fact(_)
Fact(n) == IF n = 0 THEN 1 ELSE n * Fact(n - 1)

MapPlusOne(U) ==
  LET plus1(t) == t + 1
  IN { plus1(t) : t \in U }

IdFun(U) == [u \in U |-> u]

Bump(f_, k) == [f_ EXCEPT ![k] = @ + 1]

Rec(a, b) == [a |-> a, b |-> b]

Tuple3(a, b, c) == <<a, b, c>>

Power(U) == SUBSET U

BigUnion(A) == UNION A

CaseExample(u) ==
  CASE u \in Nat -> u + 1
    [] u \in Int \ Nat -> -u
    [] OTHER -> 0

IfElseExample(b, e1, e2) == IF b THEN e1 ELSE e2

ChooseAnyFrom(U) == CHOOSE u \in U : TRUE

UnboundedChoose == CHOOSE z1 : z1 = x

Dom(f_) == DOMAIN f_

Range(f_) == { f_[i] : i \in DOMAIN f_ }

ConstFun(U, v) == [U -> {v}]

SeqStuff(U) ==
  LET s0 == << >> \o <<1>> \o <<2, 3>>
  IN  /\ s0 \in Seq(Int)
      /\ Len(s0) = 3
      /\ Head(s0) = 1
      /\ Tail(s0) = <<2, 3>>
      /\ Append(<<2, 3>>, 4) = <<2, 3, 4>>
      /\ SubSeq(<<1, 2, 3, 4>>, 2, 3) = <<2, 3>>
      /\ SelectSeq(<<1, 2, 3, 4>>, LAMBDA i : i % 2 = 0) = <<2, 4>>

UpdateExamples ==
  LET r0 == [a |-> 0, b |-> {1}]
      f0 == [i \in 1..3 |-> i]
  IN  /\ [r0 EXCEPT !.b = @ \cup {2}] = [a |-> 0, b |-> {1, 2}]
      /\ [f0 EXCEPT ![2] = 42, ![3] = @ + 1][3] = 4
      /\ DOMAIN f0 = 1..3

QuantExamples(U) ==
  /\ \A u \in U : u = u
  /\ \E u \in U : u \in U
  /\ \A s1 \in SUBSET U : s1 \subseteq U
  /\ \A <<a, b>> \in U \X U : a \in U /\ b \in U

InfixUse == Equal(1, 1)

(****************************************************************)
(* State predicates and actions                                  *)
(****************************************************************)

TypeInv ==
  /\ x \in Nat
  /\ y \in 0..N
  /\ z \subseteq S
  /\ DOMAIN f = 1..N /\ \A i \in 1..N : f[i] \in Int
  /\ r \in [a : Nat, b : SUBSET S]
  /\ s \in Seq(S)
  /\ q \in BOOLEAN

Init ==
  /\ x = 0
  /\ y \in 0..N
  /\ z \in SUBSET S
  /\ f = [i \in 1..N |-> i]
  /\ r = [a |-> 0, b |-> {}]
  /\ s = << >>
  /\ q = FALSE

IncX      == x' = x + 1
DecX      == x' = x - 1
ToggleQ   == q' = ~q
AssignY   == \E n \in 0..N : y' = n
UpdateZ   == \E e \in S : z' = z \cup {e}
BumpFAny  == \E i \in DOMAIN f : f' = [f EXCEPT ![i] = @ + 1]
UpdateR   == r' = [r EXCEPT !.a = @ + 1, !.b = @ \cup {x}]
AppendS   == \E e \in S : s' = Append(s, e)

Stutter   == UNCHANGED << x, y, z, f, r, s, q >>

Next ==
  \/ (IncX    /\ UNCHANGED << y, z, f, r, s, q >>)
  \/ (ToggleQ /\ UNCHANGED << x, y, z, f, r, s >>)
  \/ (AssignY /\ UNCHANGED << x, z, f, r, s, q >>)
  \/ (UpdateZ /\ UNCHANGED << x, y, f, r, s, q >>)
  \/ (BumpFAny/\ UNCHANGED << x, y, z, r, s, q >>)
  \/ (UpdateR /\ UNCHANGED << x, y, z, f, s, q >>)
  \/ (AppendS /\ UNCHANGED << x, y, z, f, r, q >>)
  \/ Stutter

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(IncX) /\ SF_vars(AssignY)

Invariance    == [] TypeInv
LeadsToExample == (x < N) ~> (x = N)

EnablementExample ==
  /\ ENABLED IncX
  /\ ~ ENABLED DecX

---- MODULE SimpleImported ----
EXTENDS Naturals, Sequences

CONSTANTS K, U

Double(k) == 2 * k
USeq == Seq(U)
IdU == [u \in U |-> u]

RECURSIVE SumTo(_)
SumTo(n) == IF n = 0 THEN 0 ELSE n + SumTo(n - 1)
====

(****************************************************************)
(* INSTANCE usage (qualified operators)                          *)
(****************************************************************)
\*INSTANCE SimpleImported WITH K <- N, U <- S

\*ImportedUse(n) ==
\*  /\ SimpleImported!Double(n) = 2 * n
\*  /\ SimpleImported!IdU \in [S -> S]

(****************************************************************)
(* Some numeric/set expressions to touch more operators          *)
(****************************************************************)
MoreMath ==
  LET a == N + 1
      b == (N \div 2)
      c == (N % 2)
  IN  /\ a > N
      /\ b \in Nat
      /\ c \in {0, 1}

SetCalcs ==
  LET A == { i \in 1..N : i % 2 = 0 }
      B == { i \in 1..N : i % 2 = 1 }
  IN  /\ A \cap B = {}
      /\ A \cup B = 1..N
      /\ A \ B \subseteq A
      /\ Cardinality(SUBSET {1,2}) = 4

====

