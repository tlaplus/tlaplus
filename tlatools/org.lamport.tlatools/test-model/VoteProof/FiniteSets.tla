---------------------------- MODULE FiniteSets -----------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
  (*************************************************************************)
  (* Imports the definitions from Naturals and Sequences, but doesn't      *)
  (* export them.                                                          *)
  (*************************************************************************)

IsFiniteSet(S) == 
  (*************************************************************************)
  (* A set S is finite iff there is a finite sequence containing all its   *)
  (* elements.                                                             *)
  (*************************************************************************)
  \E seq \in Seq(S) : \A s \in S : \E n \in 1..Len(seq) : seq[n] = s

Cardinality(S) ==
  (*************************************************************************)
  (* Cardinality is defined only for finite sets.                          *)
  (*************************************************************************)
  LET CS[T \in SUBSET S] == IF T = {} THEN 0
                                      ELSE 1 + CS[T \ {CHOOSE x : x \in T}]
  IN  CS[S]
=============================================================================
