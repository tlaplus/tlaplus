-------------------------- MODULE QueensPlusCal -----------------------------
EXTENDS Naturals, Sequences
(***************************************************************************)
(* Formulation of the N-queens problem and an iterative algorithm to solve *)
(* the problem in TLA+. Since there must be exactly one queen in every row *)
(* we represent placements of queens as functions of the form              *)
(*    queens \in [ 1..N -> 1..N ]                                          *)
(* where queens[i] gives the column of the queen in row i. Note that such  *)
(* a function is just a sequence of length N.                              *)
(* We will also consider partial solutions, also represented as sequences  *)
(* of length \leq N.                                                       *)
(***************************************************************************)

CONSTANT N              \** number of queens and size of the board
ASSUME N \in Nat \ {0}

(* The following predicate determines if queens i and j attack each other
   in a placement of queens (represented by a sequence as above). *)
Attacks(queens,i,j) ==
  \/ queens[i] = queens[j]                 \** same column
  \/ queens[i] - queens[j] = i - j         \** first diagonal
  \/ queens[j] - queens[i] = i - j         \** second diagonal

(* A placement represents a (partial) solution if no two different queens
   attack each other in it. *)
IsSolution(queens) ==
  \A i \in 1 .. Len(queens)-1 : \A j \in i+1 .. Len(queens) : 
       ~ Attacks(queens,i,j) 

(* Compute the set of solutions of the N-queens problem. *)
Solutions == { queens \in [1..N -> 1..N] : IsSolution(queens) }

(***************************************************************************)
(* We now describe an algorithm that iteratively computes the set of       *)
(* solutions of the N-queens problem by successively placing queens.       *)
(* The current state of the algorithm is given by two variables:           *)
(* - todo contains a set of partial solutions,                             *)
(* - sols contains the set of full solutions found so far.                 *)
(* At every step, the algorithm picks some partial solution and computes   *)
(* all possible extensions by the next queen. If N queens have been placed *)
(* these extensions are in fact full solutions, otherwise they are added   *)
(* to the set todo.                                                        *)
(***************************************************************************)

(* --algorithm Queens
     variables
       todo = { << >> };
       sols = {};

     begin
nxtQ:  while todo # {}
       do
         with queens \in todo,
              nxtQ = Len(queens) + 1,
              cols = { c \in 1..N : ~ \E i \in 1 .. Len(queens) :
                                      Attacks( Append(queens, c), i, nxtQ ) },
              exts = { Append(queens,c) : c \in cols }
         do
           if (nxtQ = N)
           then todo := todo \ {queens}; sols := sols \union exts;
           else todo := (todo \ {queens}) \union exts;
           end if;
         end with;
       end while;
     end algorithm
*)

\** BEGIN TRANSLATION
VARIABLES todo, sols, pc

vars == << todo, sols, pc >>

Init == (* Global variables *)
        /\ todo = { << >> }
        /\ sols = {}
        /\ pc = "nxtQ"

nxtQ == /\ pc = "nxtQ"
        /\ IF todo # {}
              THEN /\ \E queens \in todo:
                        LET nxtQ == Len(queens) + 1 IN
                          LET cols == { c \in 1..N : ~ \E i \in 1 .. Len(queens) :
                                                       Attacks( Append(queens, c), i, nxtQ ) } IN
                            LET exts == { Append(queens,c) : c \in cols } IN
                              IF (nxtQ = N)
                                 THEN /\ todo' = todo \ {queens}
                                      /\ sols' = (sols \union exts)
                                 ELSE /\ todo' = ((todo \ {queens}) \union exts)
                                      /\ UNCHANGED sols
                   /\ pc' = "nxtQ"
              ELSE /\ pc' = "Done"
                   /\ UNCHANGED << todo, sols >>

Next == nxtQ
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\** END TRANSLATION

TypeInvariant ==
  /\ todo \in SUBSET Seq(1 .. N) /\ \A s \in todo : Len(s) < N
  /\ sols \in SUBSET Seq(1 .. N) /\ \A s \in sols : Len(s) = N

(* The set of sols contains only solutions, and contains all solutions
   when todo is empty. *)
Invariant ==
  /\ sols \subseteq Solutions
  /\ todo = {} => Solutions \subseteq sols

(* Assert that no solutions are ever computed so that TLC displays one *)
NoSolutions == sols = {}

(* Add a fairness condition to ensure progress as long as todo is nonempty *)
Liveness == WF_vars(nxtQ)
LiveSpec == Spec /\ Liveness

=============================================================================
\* Modification History
\* Last modified Sat Dec 18 18:57:03 CET 2010 by merz
\* Created Sat Dec 11 08:50:24 CET 2010 by merz
