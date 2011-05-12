---- MODULE FiniteSets ----
(*`^\addcontentsline{toc}{section}{FiniteSets}^'*)

EXTENDS Stubs,Naturals,Sequences
(* Should be LOCAL INSTANCE *)

(* Should be LOCAL INSTANCE *)

(*Defn*)IsFiniteSet(S)==
  \E seq \in Seq(S):(\A s \in S:(\E n \in 1..Len(seq):seq[n]=s))

(*Defn*)Cardinality(S)==
  LET
    (*Defn*)CS[T \in SUBSET S]==IF T={}THEN 0 ELSE 1+CS[(T \ {CHOOSE x:x \in T})]
  IN
    CS[S]
====
