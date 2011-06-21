-------------------------- MODULE TransitiveClosure -------------------------
(***************************************************************************)
(* Mathematicians define a relation R to be a set of ordered pairs, and    *)
(* write `s R t' to mean `<<s, t>> \in R'.  The transitive closure TC(R)   *)
(* of the relation R is the smallest relation containg R such that,        *)
(*  `s TC(R) t' and `t TC(R) u' imply `s TC(R) u', for any s, t, and u.    *)
(* This module shows several ways of defining the operator TC.             *)
(*                                                                         *)
(* Mathematicians say that R is a relation on a set S iff R is a subset of *)
(* S \X S.  Let the `support' of a relation R be the set of all elements s *)
(* such that `s R t' or `t R s' for some t.  Then any relation is a        *)
(* relation on its support.  Moreover, the support of R is the support of  *)
(* TC(R).  So, to define the transitive closure of R, there's no need to   *)
(* say what set R is a relation on.                                        *)
(*                                                                         *)
(* Let's begin by importing some modules we'll need and defining the the   *)
(* support of a relation.                                                  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

Support(R) == {r[1] : r \in R} \cup {r[2] : r \in R}

(***************************************************************************)
(* A relation R defines a directed graph on its support, where there is an *)
(* edge from s to t iff `s R t'.  We can define TC(R) to be the relation   *)
(* such that `s R t' holds iff there is a path from s to t in this graph.  *)
(* We represent a path by the sequence of nodes on the path, so the length *)
(* of the path (the number of edges) is one greater than the length of the *)
(* sequence.  We then get the following definition of TC.                  *)
(***************************************************************************)
TC(R) == 
  LET S == Support(R)     
  IN  {<<s, t>> \in S \X S :
        \E p \in Seq(S) : /\ Len(p) > 1
                          /\ p[1] = s
                          /\ p[Len(p)] = t
                          /\ \A i \in  1..(Len(p)-1) : <<p[i], p[i+1]>> \in R}

(***************************************************************************)
(* This definition can't be evaluated by TLC because Seq(S) is an infinite *)
(* set.  However, it's not hard to see that if R is a finite set, then it  *)
(* suffices to consider paths whose length is at most Cardinality(S).      *)
(* Modifying the definition of TC we get the following definition that     *)
(* defines TC1(R) to be the transitive closure of R, if R is a finite set. *)
(* The LET expression defines BoundedSeq(S, n) to be the set of all        *)
(* sequences in Seq(S) of length at most n.                                *)
(***************************************************************************)
TC1(R) == 
  LET BoundedSeq(S, n) == UNION {[1..i -> S] : i \in 0..n}
      S == Support(R)     
  IN  {<<s, t>> \in S \X S :
                    \E p \in BoundedSeq(S, Cardinality(S)+1) : 
                            /\ Len(p) > 1
                            /\ p[1] = s
                            /\ p[Len(p)] = t
                            /\ \A i \in  1..(Len(p)-1) : <<p[i], p[i+1]>> \in R}

(***************************************************************************)
(* This naive method used by TLC to evaluate expressions makes this        *)
(* definition rather inefficient.  (As an exercise, find an upper bound on *)
(* its complexity.) A definition of TC(R) that TLC can evaluate more       *)
(* efficiently is obtained by recursively defining the function C with     *)
(* domain Nat such that C[n] is the set of all pairs <<s, t>> with s, t    *)
(* \in Support(R) such that there exists a path of length at most n+1 from *)
(* s to t in Support(R).  This leads to the following definition, which    *)
(* essentially implements Warshall's algorithm.                            *)
(***************************************************************************)
TC2(R) ==
  LET S == Support(R)
      C[n \in Nat] == IF n = 0 THEN R
                               ELSE C[n-1] \cup
                                     {<<s, t>> \in S \X S :
                                         \E u \in S : /\ <<s, u>> \in C[n-1]
                                                      /\ <<u, t>> \in R }
  IN  IF S = {} THEN {} ELSE C[Cardinality(S) - 1] 

(***************************************************************************)
(* We can modify this definition as follows to be somewhat more efficient: *)
(***************************************************************************)
TC3(R) ==
  LET S == Support(R)
      C[n \in Nat] == IF n = 0 THEN R
                               ELSE C[n-1] \cup
                                     {<<s, t>> \in S \X S :
                                         \E u \in S : /\ <<s, u>> \in C[n-1]
                                                      /\ <<u, t>> \in C[n-1] }
  IN  IF S = {} THEN {} ELSE C[(Cardinality(S) \div 2)+ 1] 

(***************************************************************************)
(* These definitions of TC1, TC2, and TC3 are somewhat unsatisfactory      *)
(* because of their use of Cardinality(S).  For example, it would be easy  *)
(* to make a mistake and use Cardinality(S) instead of Cardinality(S)+1 in *)
(* the definition of TC1(R).  The following definition is obtained from    *)
(* the basic idea of TC3 by removing the recursive LET definition of C and *)
(* making the entire definition recursive.  I find it more elegant than    *)
(* the preceding three definitions.                                        *)
(***************************************************************************)
RECURSIVE TC4(_)
TC4(R) ==
  LET R1 == {r[1] : r \in R}
      R2 == {r[2] : r \in R}
      RR == {<<s, t>> \in R1 \X R2 : 
                \E u \in R1 \cap R2 : (<<s, u>> \in R) /\ (<<u, t>> \in R)}
  IN  IF RR \subseteq R THEN R
                        ELSE TC4(R \cup RR)
  

(***************************************************************************)
(* We now test that these four definitions are equivalent.  Since it's     *)
(* unlikely that all four are wrong in the same way, their equivalence     *)
(* makes it highly probable that they're correct.                          *)
(***************************************************************************)
ASSUME \A N \in 0..3 : 
          \A R \in SUBSET ((1..N) \X (1..N)) : /\ TC1(R) = TC2(R)
                                               /\ TC2(R) = TC3(R) 
                                               /\ TC3(R) = TC4(R)

(***************************************************************************)
(* Sometimes it's more convenient to represent a relation as a             *)
(* Boolean-valued operator, so we can write `s R t' as R(s, t).  When      *)
(* represented this way, we have to know what set R is an operator on,     *)
(* because we can't define its support in TLA+.  Also, since TLA+ does not *)
(* permit us to define operator-valued operators, we cannot define TC(R)   *)
(* to be an operator.  Instead, we define TC5(R, S, s, t) to mean that the *)
(* transitive closure of R is true on s and t, where the operator R        *)
(* represents a relation on S.  For any particular R, we can then define   *)
(* its transitive closure to be the operator TCR defined by                *)
(*                                                                         *)
(*    TCR(s, t) == TC5(R, S, s, t)                                         *)
(***************************************************************************)
TC5(R(_,_), S, s, t) ==
  LET CR[n \in Nat, v \in S] == 
          IF n = 0 THEN R(s, v)
                   ELSE \/ CR[n-1, v] 
                        \/ \E u \in S : CR[n-1, u] /\ R(u, v)
  IN  /\ s \in S
      /\ t \in S
      /\ CR[Cardinality(S)-1, t]


(***************************************************************************)
(* Finally, the following assumption checks that our definition of TC5     *)
(* agrees with our definition TC1.                                         *)
(***************************************************************************)
ASSUME \A N \in 0..3 : \A R \in SUBSET ((1..N) \X (1..N)) :
         LET RR(s, t) == <<s, t>> \in R
             S == Support(R)
         IN  \A s, t \in S : 
                TC5(RR, S, s, t) <=> (<<s, t>> \in TC1(R))
=============================================================================
