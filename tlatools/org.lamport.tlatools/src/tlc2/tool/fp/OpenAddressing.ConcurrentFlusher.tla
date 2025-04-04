------------------------------- MODULE Merge -------------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets

(**********************************)
(* The larger of the two elements *)
(**********************************)
Max(a,b) == IF a > b THEN a ELSE b

(***************************************************************************)
(* The image of the function F.                                            *)
(***************************************************************************)
Image(F) == { F[x] : x \in DOMAIN F }

(***************************************************************************)
(* Convertes the given Sequence seq into a Set of all the                  *) 
(* Sequence's elements. In other words, the image of the function          *)
(* that seq is.                                                            *)
(***************************************************************************)
SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)} 

(***************************************************************************)
(* Returns a Set of all possible permutations with distinct elemenents     *)
(* created out of the elements of Set set. All elements of set occur in    *)
(* in the sequence.                                                        *)
(***************************************************************************)
IsOrdered(seq) == IF seq = <<>> \/ Len(seq) = 1 THEN TRUE ELSE
                     \A i \in 1..(Len(seq) - 1): seq[i] < seq[i+1]
OrderedSequences(set) == UNION {{perm \in [1..Cardinality(set) -> set]: 
                                   IsOrdered(perm)}}

(***
--fair algorithm Merge {

  variables history = {},
            a = 0,
            aLength = 0,
            A = <<>>,
            b = 0,
            bLength = 0,
            B = <<>>,
            O = <<>>; 
            
    define {
       Inv == /\ Image(O) \subseteq history
              /\ IsOrdered(O)
       NoDuplicates == Image(A) \cap Image(B) = {}
    }
    
    macro Consume(var, seq) {
         var := Head(seq);
         seq := Tail(seq);
    }
  {

  (* Initialize A and B with all possible combination of sorted sequences. *)
  init:           
    with (r \in SUBSET Nat \ {{}}) {
       with (s \in ((SUBSET (Nat)) \ {{}})) {
           with (t \in OrderedSequences(s) \cup {<<>>}) {
               B := t;
               bLength := Len(B);
               with (u \in OrderedSequences(r) \cup {<<>>}) {
                    A := u;
                    aLength := Len(A);
               }
           };
       };  
    };
  
  (* Keep history. *)
  hstry:
     history := SeqToSet(A) \cup SeqToSet(B);
     if (Cardinality(history) = 0) {
        goto "Done";
     };
       
  (* Merge sorted A and B to obtain sorted O. *)
  mrg1: 
     if (aLength > 0) {
         Consume(a, A);
     };
     if (bLength > 0) {
         Consume(b, B);
     };
     
  mrg2:
        if (a = b) {
           O := Append(O, a);
           aLength := aLength - 1;
           if (aLength > 0) {
             Consume(a, A);
           };
           bLength := bLength - 1;
           if (bLength > 0) {
             Consume(b, B);
           };
        };
  mrg2a:
        if (aLength > 0 /\ (a < b \/ bLength = 0)) {
           O := Append(O, a);
           aLength := aLength - 1;
           if (aLength > 0) {
             Consume(a, A);
           };
        };
  mrg2b:     
        if (bLength > 0 /\ (b < a \/ aLength = 0)) {
           O := Append(O, b);
           bLength := bLength - 1;
           if (bLength > 0) {
             Consume(b, B);
           };
        };
   mrg3:     
        if (bLength > 0 \/ aLength > 0) {
           goto mrg2;
        };
   mrg4:
       assert bLength = 0 /\ aLength = 0;
       assert Len(O) = Cardinality(history);
       assert Image(O) = history;
   }
}

***     this ends the comment containg the pluscal code      **********)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "8099c642")
VARIABLES pc, history, a, aLength, A, b, bLength, B, O

(* define statement *)
Inv == /\ Image(O) \subseteq history
       /\ IsOrdered(O)
NoDuplicates == Image(A) \cap Image(B) = {}


vars == << pc, history, a, aLength, A, b, bLength, B, O >>

Init == (* Global variables *)
        /\ history = {}
        /\ a = 0
        /\ aLength = 0
        /\ A = <<>>
        /\ b = 0
        /\ bLength = 0
        /\ B = <<>>
        /\ O = <<>>
        /\ pc = "init"

init == /\ pc = "init"
        /\ \E r \in SUBSET Nat \ {{}}:
             \E s \in ((SUBSET (Nat)) \ {{}}):
               \E t \in OrderedSequences(s) \cup {<<>>}:
                 /\ B' = t
                 /\ bLength' = Len(B')
                 /\ \E u \in OrderedSequences(r) \cup {<<>>}:
                      /\ A' = u
                      /\ aLength' = Len(A')
        /\ pc' = "hstry"
        /\ UNCHANGED << history, a, b, O >>

hstry == /\ pc = "hstry"
         /\ history' = (SeqToSet(A) \cup SeqToSet(B))
         /\ IF Cardinality(history') = 0
               THEN /\ pc' = "Done"
               ELSE /\ pc' = "mrg1"
         /\ UNCHANGED << a, aLength, A, b, bLength, B, O >>

mrg1 == /\ pc = "mrg1"
        /\ IF aLength > 0
              THEN /\ a' = Head(A)
                   /\ A' = Tail(A)
              ELSE /\ TRUE
                   /\ UNCHANGED << a, A >>
        /\ IF bLength > 0
              THEN /\ b' = Head(B)
                   /\ B' = Tail(B)
              ELSE /\ TRUE
                   /\ UNCHANGED << b, B >>
        /\ pc' = "mrg2"
        /\ UNCHANGED << history, aLength, bLength, O >>

mrg2 == /\ pc = "mrg2"
        /\ IF a = b
              THEN /\ O' = Append(O, a)
                   /\ aLength' = aLength - 1
                   /\ IF aLength' > 0
                         THEN /\ a' = Head(A)
                              /\ A' = Tail(A)
                         ELSE /\ TRUE
                              /\ UNCHANGED << a, A >>
                   /\ bLength' = bLength - 1
                   /\ IF bLength' > 0
                         THEN /\ b' = Head(B)
                              /\ B' = Tail(B)
                         ELSE /\ TRUE
                              /\ UNCHANGED << b, B >>
              ELSE /\ TRUE
                   /\ UNCHANGED << a, aLength, A, b, bLength, B, O >>
        /\ pc' = "mrg2a"
        /\ UNCHANGED history

mrg2a == /\ pc = "mrg2a"
         /\ IF aLength > 0 /\ (a < b \/ bLength = 0)
               THEN /\ O' = Append(O, a)
                    /\ aLength' = aLength - 1
                    /\ IF aLength' > 0
                          THEN /\ a' = Head(A)
                               /\ A' = Tail(A)
                          ELSE /\ TRUE
                               /\ UNCHANGED << a, A >>
               ELSE /\ TRUE
                    /\ UNCHANGED << a, aLength, A, O >>
         /\ pc' = "mrg2b"
         /\ UNCHANGED << history, b, bLength, B >>

mrg2b == /\ pc = "mrg2b"
         /\ IF bLength > 0 /\ (b < a \/ aLength = 0)
               THEN /\ O' = Append(O, b)
                    /\ bLength' = bLength - 1
                    /\ IF bLength' > 0
                          THEN /\ b' = Head(B)
                               /\ B' = Tail(B)
                          ELSE /\ TRUE
                               /\ UNCHANGED << b, B >>
               ELSE /\ TRUE
                    /\ UNCHANGED << b, bLength, B, O >>
         /\ pc' = "mrg3"
         /\ UNCHANGED << history, a, aLength, A >>

mrg3 == /\ pc = "mrg3"
        /\ IF bLength > 0 \/ aLength > 0
              THEN /\ pc' = "mrg2"
              ELSE /\ pc' = "mrg4"
        /\ UNCHANGED << history, a, aLength, A, b, bLength, B, O >>

mrg4 == /\ pc = "mrg4"
        /\ Assert(bLength = 0 /\ aLength = 0, 
                  "Failure of assertion at line 119, column 8.")
        /\ Assert(Len(O) = Cardinality(history), 
                  "Failure of assertion at line 120, column 8.")
        /\ Assert(Image(O) = history, 
                  "Failure of assertion at line 121, column 8.")
        /\ pc' = "Done"
        /\ UNCHANGED << history, a, aLength, A, b, bLength, B, O >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == init \/ hstry \/ mrg1 \/ mrg2 \/ mrg2a \/ mrg2b \/ mrg3 \/ mrg4
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Jan 10 20:39:04 CEST 2025 by markus
\* Created Mon Jun 05 23:14:05 CEST 2017 by markus

----- CONFIG Merge -----
SPECIFICATION
    Spec

INVARIANT
    Inv
    \* NoDuplicates

PROPERTIES 
    Termination

CONSTANT
    Nat = {1,2,3,4,5}
======
