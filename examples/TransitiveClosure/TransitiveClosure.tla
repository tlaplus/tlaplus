-------------------------- MODULE TransitiveClosure -------------------------
(***************************************************************************)
(* Mathematicians define a relation R to be a set of ordered pairs, and    *)
(* write `s R t' to mean `<<s, t>> \in R'.  The transitive closure TC(R)   *)
(* of the relation R is the smallest relation containg R such that,        *)
(* `s TC(R) t' and `t TC(R) u' imply `s TC(R) u', for any s, t, and u.     *)
(* This module shows several ways of defining the operator TC.             *)
(*                                                                         *)
(* It is sometimes more convenient to represent a relation as a            *)
(* Boolean-valued function of two arguments, where `s R t' means R[s, t].  *)
(* It is a straightforward exercise to translate everything in this module *)
(* to that representation.                                                 *)
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
EXTENDS Integers, Sequences, FiniteSets, TLC

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
(* its complexity.) To obtain a definition that TLC can evaluate more      *)
(* efficiently, let's look at the closure operation more algebraically.    *)
(* Let's define the composition of two relations R and T as follows.       *)
(***************************************************************************)
R ** T == LET SR == Support(R)
              ST == Support(T)
          IN  {<<r, t>> \in SR \X ST : 
                \E s \in SR \cap ST : (<<r, s>> \in R) /\ (<<s, t>> \in T)}
                                         
(***************************************************************************)
(* We can then define the closure of R to equal                            *)
(*                                                                         *)
(*    R \cup (R ** R) \cup (R ** R ** R) \cup ...                          *)
(*                                                                         *)
(* For R finite, this union converges to the transitive closure when the   *)
(* number of terms equals the cardinality of the support of R.  This leads *)
(* to the following definition.                                            *)
(***************************************************************************)
TC2(R) ==
  LET C[n \in Nat] == IF n = 0 THEN R
                               ELSE C[n-1] \cup (C[n-1] ** R)
  IN  IF R = {} THEN {} ELSE C[Cardinality(Support(R)) - 1] 

(***************************************************************************)
(* These definitions of TC1 and TC2 are somewhat unsatisfactory because of *)
(* their use of Cardinality(S).  For example, it would be easy to make a   *)
(* mistake and use Cardinality(S) instead of Cardinality(S)+1 in the       *)
(* definition of TC1(R).  I find the following definition more elegant     *)
(* than the preceding two.  It is also more asymptotically more efficient  *)
(* because it makes O(log Cardinality (S)) rather than O(Cardinality(S))   *)
(* recursive calls.                                                        *)
(***************************************************************************)
RECURSIVE TC3(_)
TC3(R) == LET RR == R ** R
          IN  IF RR \subseteq R THEN R ELSE TC3(R \cup RR)

(***************************************************************************)
(* The preceding two definitions can be made slightly more efficient to    *)
(* execute by expanding the definition of ** and making some simple        *)
(* optimizations.  But, this is unlikely to be worth complicating the      *)
(* definitions for.                                                        *)
(*                                                                         *)
(* The following definition is (asymptotically) the most efficient.  It is *)
(* essentially the TLA+ representation of Warshall's algorithm.            *)
(* (Warshall's algorithm is typically written as an iterative procedure    *)
(* for the case of a relation on a set i..j of integers, when the relation *)
(* is represented as a Boolean-valued function.)                           *)
(***************************************************************************)
TC4(R) ==
  LET S == Support(R)
      RECURSIVE TCR(_)
      TCR(T) == IF T = {} 
                  THEN R
                  ELSE LET r == CHOOSE s \in T : TRUE
                           RR == TCR(T \ {r})
                       IN  RR \cup {<<s, t>> \in S \X S : 
                                      <<s, r>> \in RR /\ <<r, t>> \in RR}
  IN  TCR(S)
  
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
(* Sometimes we want to represent a relation as a Boolean-valued operator, *)
(* so we can write `s R t' as R(s, t).  This representation is less        *)
(* convenient for manipulating relations, since an operator is not an      *)
(* ordinary value the way a function is.  For example, since TLA+ does not *)
(* permit us to define operator-valued operators, we cannot define a       *)
(* transitive closure operator TC so TC(R) is the operator that represents *)
(* the transitive closure.  Moreover, an operator R by itself cannot       *)
(* represent a relation; we also have to know what set it is an operator   *)
(* on.  (If R is a function, its domain tells us that.)                    *)
(*                                                                         *)
(* However, there may be situations in which you want to represent         *)
(* relations by operators.  In that case, you can define an operator TC so *)
(* that, if R is an operator representing a relation on S, and TCR is the  *)
(* operator representing it transitive closure, then                       *)
(*                                                                         *)
(*   TCR(s, t) = TC(R, S, s, t)                                            *)
(*                                                                         *)
(* for all s, t.  Here is the definition.  (This assumes that for an       *)
(* operator R on a set S, R(s, t) equals FALSE for all s and t not in S.)  *)
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
(* Finally, the following assumption checks that our definition TC5 agrees *)
(* with our definition TC1.                                                *)
(***************************************************************************)
ASSUME \A N \in 0..3 : \A R \in SUBSET ((1..N) \X (1..N)) :
         LET RR(s, t) == <<s, t>> \in R
             S == Support(R)
         IN  \A s, t \in S : 
                TC5(RR, S, s, t) <=> (<<s, t>> \in TC1(R))
=============================================================================
