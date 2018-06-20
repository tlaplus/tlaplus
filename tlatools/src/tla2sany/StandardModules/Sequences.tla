------------------------------ MODULE Sequences -----------------------------
(***************************************************************************)
(* Defines operators on finite sequences, where a sequence of length n is  *)
(* represented as a function whose domain is the set 1..n (the set         *)
(* {1, 2, ... , n}).  This is also how TLA+ defines an n-tuple, so         *)
(* tuples are sequences.                                                   *)
(***************************************************************************)

LOCAL INSTANCE Naturals
  (*************************************************************************)
  (* Imports the definitions from Naturals, but don't export them.         *)
  (*************************************************************************)
  
Seq(S) == UNION {[1..n -> S] : n \in Nat} \* tlc2.module.Sequences.Seq(Value)
  (*************************************************************************)
  (* The set of all sequences of elements in S.                            *)
  (*************************************************************************)

Len(s) == CHOOSE n \in Nat : DOMAIN s = 1..n \* tlc2.module.Sequences.Len(Value)
  (*************************************************************************)
  (* The length of sequence s.                                             *)
  (*************************************************************************)

s \o t == [i \in 1..(Len(s) + Len(t)) |-> IF i \leq Len(s) THEN s[i]
                                                           ELSE t[i-Len(s)]] \* tlc2.module.Sequences.Concat(Value, Value)
  (*************************************************************************)
  (* The sequence obtained by concatenating sequences s and t.             *)
  (*************************************************************************)

Append(s, e) == s \o <<e>> \* tlc2.module.Sequences.Append(Value, Value)
  (**************************************************************************)
  (* The sequence obtained by appending element e to the end of sequence s. *)
  (**************************************************************************)

Head(s) == s[1] \* tlc2.module.Sequences.Head(Value)
Tail(s) == CASE s # << >> -> [i \in 1..(Len(s)-1) |-> s[i+1]] \* tlc2.module.Sequences.Tail(Value)
  (*************************************************************************)
  (* The usual head (first) and tail (rest) operators. (Definition of Tail *)
  (* changed on 4 Jun 2013 because original defined Tail(<< >>) = << >> .  *)
  (*************************************************************************)

SubSeq(s, m, n) == [i \in 1..(1+n-m) |-> s[i+m-1]] \* tlc2.module.Sequences.SubSeq(Value, Value, Value)
  (*************************************************************************)
  (* The sequence <<s[m], s[m+1], ... , s[n]>>.                            *)
  (*************************************************************************)
  
SelectSeq(s, Test(_)) == 
  (*************************************************************************)
  (* The subsequence of s consisting of all elements s[i] such that        *)
  (* Test(s[i]) is true.                                                   *)
  (*************************************************************************)
  LET F[i \in 0..Len(s)] == 
        (*******************************************************************)
        (* F[i] equals SelectSeq(SubSeq(s, 1, i), Test]                    *)
        (*******************************************************************)
        IF i = 0 THEN << >>
                 ELSE IF Test(s[i]) THEN Append(F[i-1], s[i])
                                    ELSE F[i-1]
  IN F[Len(s)] \* tlc2.module.Sequences.SelectSeq(Value, Value)
=============================================================================
