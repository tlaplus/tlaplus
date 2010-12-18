------------------------------- MODULE Queens -------------------------------
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

VARIABLES todo, sols

Init == /\ todo = { << >> }   \** << >> is a partial (but not full) solution
        /\ sols = {}          \** no full solution found so far

PlaceQueen == \E queens \in todo :
  \** extend some partial solution by placing the next queen
  LET nxtQ == Len(queens) + 1   \** number of queen to place
      cols == \** set of columns on which queen can be placed without any
              \** conflict with some queen already placed
              { c \in 1..N : ~ \E i \in 1 .. Len(queens) :
                                  Attacks( Append(queens, c), i, nxtQ ) }
      exts == { Append(queens, c) : c \in cols }  \** possible extensions
  IN  IF nxtQ = N  \** completed solution
      THEN /\ todo' = todo \ {queens}
           /\ sols' = sols \union exts
      ELSE /\ todo' = (todo \ {queens}) \union exts
           /\ sols' = sols

vars == <<todo,sols>>
Spec == Init /\ [][PlaceQueen]_vars /\ WF_vars(PlaceQueen)

TypeInvariant ==
  /\ todo \in SUBSET Seq(1 .. N) /\ \A s \in todo : Len(s) < N
  /\ sols \in SUBSET Seq(1 .. N) /\ \A s \in sols : Len(s) = N

(* The set of sols contains only solutions, and contains all solutions
   when todo is empty. *)
Invariant ==
  /\ sols \subseteq Solutions
  /\ todo = {} => Solutions \subseteq sols

Termination == <>(todo = {})

(* Assert that no solutions are ever computed so that TLC displays one *)
NoSolutions == sols = {}

=============================================================================
\* Modification History
\* Last modified Sat Dec 11 09:58:48 CET 2010 by merz
\* Created Sat Dec 11 08:50:24 CET 2010 by merz
