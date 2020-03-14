---- MODULE TLC ----
(*`^\addcontentsline{toc}{section}{TLC}^'*)

EXTENDS Sequences
(*  stubs for TLC defines; TLC will override these  *)

(* 
<Constant>TLCMode</Constant>
 *)

(*Defn*)TLCMode==FALSE

CONSTANT SequenceMax

(*Defn*)ArbSeq(s)==IF TLCMode THEN BSeq(s,SequenceMax)ELSE Seq(s)

(*Defn*)TLCBoundedSeq(s,n)==IF TLCMode THEN BSeq(s,n)ELSE Seq(s)

(*Defn*)Print(in,out)=={}

(*Defn*)EmptySequence==[x \in{}|->0]
====
