@!@!@STARTMSG 1000:0 @!@!@
Will generate a SpecTE file pair if error states are encountered.
@!@!@ENDMSG 1000 @!@!@
@!@!@STARTMSG 2262:0 @!@!@
TLC2 Version 2.15 of Day Month 20??
@!@!@ENDMSG 2262 @!@!@
@!@!@STARTMSG 2187:0 @!@!@
Running breadth-first search Model-Checking with fp 4 and seed 5688400317107100584 with 1 worker on 12 cores with 2428MB heap and 5460MB offheap memory [pid: 81433] (Mac OS X 10.13.6 x86_64, AdoptOpenJDK 13.0.1 x86_64, OffHeapDiskFPSet, DiskStateQueue).
@!@!@ENDMSG 2187 @!@!@
@!@!@STARTMSG 2220:0 @!@!@
Starting SANY...
@!@!@ENDMSG 2220 @!@!@
Parsing file /Users/loki/arbeit/microsoft/dev/tlaplus/runtime-org.lamport.tla.toolbox.product.product.product/QueensPluscal_1579286757638/QueensPluscal.toolbox/FourQueens/MC.tla
Parsing file /Users/loki/arbeit/microsoft/dev/tlaplus/runtime-org.lamport.tla.toolbox.product.product.product/QueensPluscal_1579286757638/QueensPluscal.toolbox/FourQueens/QueensPluscal.tla
Parsing file /Users/loki/arbeit/microsoft/dev/quaeler_repo/tlaplus/tlatools/class/tla2sany/StandardModules/TLC.tla
Parsing file /Users/loki/arbeit/microsoft/dev/quaeler_repo/tlaplus/tlatools/class/tla2sany/StandardModules/Naturals.tla
Parsing file /Users/loki/arbeit/microsoft/dev/quaeler_repo/tlaplus/tlatools/class/tla2sany/StandardModules/Sequences.tla
Parsing file /Users/loki/arbeit/microsoft/dev/quaeler_repo/tlaplus/tlatools/class/tla2sany/StandardModules/FiniteSets.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module QueensPluscal
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module MC
@!@!@STARTMSG 2219:0 @!@!@
SANY finished.
@!@!@ENDMSG 2219 @!@!@
@!@!@STARTMSG 2185:0 @!@!@
Starting... (2020-01-28 16:51:31)
@!@!@ENDMSG 2185 @!@!@
@!@!@STARTMSG 2212:0 @!@!@
Implied-temporal checking--satisfiability problem has 1 branches.
@!@!@ENDMSG 2212 @!@!@
@!@!@STARTMSG 2189:0 @!@!@
Computing initial states...
@!@!@ENDMSG 2189 @!@!@
@!@!@STARTMSG 2190:0 @!@!@
Finished computing initial states: 1 distinct state generated at 2020-01-28 16:51:32.
@!@!@ENDMSG 2190 @!@!@
@!@!@STARTMSG 2111:1 @!@!@
Evaluating invariant Invariant failed.
Attempted to apply function:
<<1, 1, 1>>
to argument 0, which is not in the domain of the function.
@!@!@ENDMSG 2111 @!@!@
@!@!@STARTMSG 2121:1 @!@!@
The behavior up to this point is:
@!@!@ENDMSG 2121 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
1: <Initial predicate>
/\ todo = {<<>>}
/\ sols = {}
/\ pc = "nxtQ"

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
2: <nxtQ line 77, col 9 to line 91, col 48 of module QueensPluscal>
/\ todo = {<<1>>, <<2>>, <<3>>}
/\ sols = {}
/\ pc = "nxtQ"

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
3: <nxtQ line 77, col 9 to line 91, col 48 of module QueensPluscal>
/\ todo = {<<2>>, <<3>>, <<1, 3>>}
/\ sols = {}
/\ pc = "nxtQ"

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
4: <nxtQ line 77, col 9 to line 91, col 48 of module QueensPluscal>
/\ todo = {<<3>>, <<1, 3>>}
/\ sols = {}
/\ pc = "nxtQ"

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
5: <nxtQ line 77, col 9 to line 91, col 48 of module QueensPluscal>
/\ todo = {<<1, 3>>, <<3, 1>>}
/\ sols = {}
/\ pc = "nxtQ"

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
6: <nxtQ line 77, col 9 to line 91, col 48 of module QueensPluscal>
/\ todo = {<<3, 1>>}
/\ sols = {}
/\ pc = "nxtQ"

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2217:4 @!@!@
7: <nxtQ line 77, col 9 to line 91, col 48 of module QueensPluscal>
/\ todo = {}
/\ sols = {}
/\ pc = "nxtQ"

@!@!@ENDMSG 2217 @!@!@
@!@!@STARTMSG 2201:0 @!@!@
The coverage statistics at 2020-01-28 16:51:32
@!@!@ENDMSG 2201 @!@!@
@!@!@STARTMSG 2773:0 @!@!@
<Init line 72, col 1 to line 72, col 4 of module QueensPluscal>: 2:2
@!@!@ENDMSG 2773 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 73, col 9 to line 75, col 22 of module QueensPluscal: 2
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2772:0 @!@!@
<nxtQ line 77, col 1 to line 77, col 4 of module QueensPluscal>: 18:45
@!@!@ENDMSG 2772 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 77, col 12 to line 77, col 22 of module QueensPluscal: 45
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 77, col 12 to line 77, col 13 of module QueensPluscal: 23
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 78, col 15 to line 78, col 23 of module QueensPluscal: 23
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 84, col 35 to line 84, col 42 of module QueensPluscal: 45
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 85, col 42 to line 85, col 64 of module QueensPluscal: 16
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 85, col 50 to line 85, col 64 of module QueensPluscal: 17
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 86, col 42 to line 86, col 67 of module QueensPluscal: 16
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 86, col 51 to line 86, col 66 of module QueensPluscal: 17
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||line 86, col 51 to line 86, col 54 of module QueensPluscal: 17
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||line 86, col 63 to line 86, col 66 of module QueensPluscal: 17
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2775:0 @!@!@
  |||line 83, col 41 to line 83, col 73 of module QueensPluscal: 17:30
@!@!@ENDMSG 2775 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||line 83, col 68 to line 83, col 71 of module QueensPluscal: 17
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2775:0 @!@!@
  |||||line 81, col 39 to line 82, col 94 of module QueensPluscal: 17:17
@!@!@ENDMSG 2775 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||line 81, col 54 to line 82, col 92 of module QueensPluscal: 51
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||||line 81, col 56 to line 82, col 92 of module QueensPluscal: 51
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||||line 82, col 56 to line 82, col 92 of module QueensPluscal: 68
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||||||line 20, col 3 to line 22, col 34 of module QueensPluscal: 68
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||||||line 20, col 6 to line 20, col 26 of module QueensPluscal: 68
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||||||line 21, col 6 to line 21, col 34 of module QueensPluscal: 51
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||||||line 22, col 6 to line 22, col 34 of module QueensPluscal: 34
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||||||line 82, col 65 to line 82, col 81 of module QueensPluscal: 68
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||||||line 82, col 84 to line 82, col 84 of module QueensPluscal: 68
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||||||line 82, col 87 to line 82, col 90 of module QueensPluscal: 68
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||||line 81, col 65 to line 81, col 80 of module QueensPluscal: 51
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||line 81, col 47 to line 81, col 50 of module QueensPluscal: 17
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 87, col 42 to line 87, col 80 of module QueensPluscal: 28
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 87, col 51 to line 87, col 79 of module QueensPluscal: 28
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||line 87, col 52 to line 87, col 66 of module QueensPluscal: 28
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||line 87, col 76 to line 87, col 79 of module QueensPluscal: 28
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2775:0 @!@!@
  |||line 83, col 41 to line 83, col 73 of module QueensPluscal: 28:71
@!@!@ENDMSG 2775 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||line 83, col 43 to line 83, col 58 of module QueensPluscal: 22
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||line 83, col 68 to line 83, col 71 of module QueensPluscal: 28
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2775:0 @!@!@
  |||||line 81, col 39 to line 82, col 94 of module QueensPluscal: 28:50
@!@!@ENDMSG 2775 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||line 81, col 54 to line 82, col 92 of module QueensPluscal: 84
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||||line 81, col 56 to line 82, col 92 of module QueensPluscal: 84
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||||line 82, col 56 to line 82, col 92 of module QueensPluscal: 78
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||||||line 20, col 3 to line 22, col 34 of module QueensPluscal: 78
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||||||line 20, col 6 to line 20, col 26 of module QueensPluscal: 78
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||||||line 21, col 6 to line 21, col 34 of module QueensPluscal: 52
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||||||line 22, col 6 to line 22, col 34 of module QueensPluscal: 35
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||||||line 82, col 65 to line 82, col 81 of module QueensPluscal: 78
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||||||line 82, col 84 to line 82, col 84 of module QueensPluscal: 78
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||||||||line 82, col 87 to line 82, col 90 of module QueensPluscal: 78
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||||line 81, col 65 to line 81, col 80 of module QueensPluscal: 84
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||||||line 81, col 47 to line 81, col 50 of module QueensPluscal: 28
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 88, col 42 to line 88, col 53 of module QueensPluscal: 28
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 79, col 37 to line 79, col 40 of module QueensPluscal: 23
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 89, col 23 to line 89, col 34 of module QueensPluscal: 44
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 90, col 23 to line 90, col 34 of module QueensPluscal: 0
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 91, col 23 to line 91, col 48 of module QueensPluscal: 0
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2772:0 @!@!@
<Terminating line 94, col 1 to line 94, col 11 of module QueensPluscal>: 0:0
@!@!@ENDMSG 2772 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 94, col 16 to line 94, col 26 of module QueensPluscal: 16
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 94, col 31 to line 94, col 44 of module QueensPluscal: 0
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2774:0 @!@!@
<TypeInvariant line 105, col 1 to line 105, col 13 of module QueensPluscal>
@!@!@ENDMSG 2774 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 106, col 3 to line 107, col 62 of module QueensPluscal: 19
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 106, col 6 to line 106, col 62 of module QueensPluscal: 19
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||line 106, col 6 to line 106, col 32 of module QueensPluscal: 19
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||line 106, col 37 to line 106, col 62 of module QueensPluscal: 19
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||line 106, col 53 to line 106, col 62 of module QueensPluscal: 34
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |||line 106, col 46 to line 106, col 49 of module QueensPluscal: 19
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 107, col 6 to line 107, col 62 of module QueensPluscal: 19
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2774:0 @!@!@
<Invariant line 111, col 1 to line 111, col 9 of module QueensPluscal>
@!@!@ENDMSG 2774 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  line 112, col 3 to line 113, col 42 of module QueensPluscal: 19
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 112, col 6 to line 112, col 29 of module QueensPluscal: 19
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  |line 113, col 6 to line 113, col 42 of module QueensPluscal: 19
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||line 113, col 6 to line 113, col 14 of module QueensPluscal: 19
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2221:0 @!@!@
  ||line 113, col 19 to line 113, col 42 of module QueensPluscal: 1
@!@!@ENDMSG 2221 @!@!@
@!@!@STARTMSG 2202:0 @!@!@
End of statistics.
@!@!@ENDMSG 2202 @!@!@
@!@!@STARTMSG 2200:0 @!@!@
Progress(7) at 2020-01-28 16:51:32: 33 states generated (968 s/min), 19 distinct states found (557 ds/min), 2 states left on queue.
@!@!@ENDMSG 2200 @!@!@
@!@!@STARTMSG 2199:0 @!@!@
33 states generated, 19 distinct states found, 2 states left on queue.
@!@!@ENDMSG 2199 @!@!@
@!@!@STARTMSG 2194:0 @!@!@
The depth of the complete state graph search is 7.
@!@!@ENDMSG 2194 @!@!@
@!@!@STARTMSG 2268:0 @!@!@
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 3 and the 95th percentile is 3).
@!@!@ENDMSG 2268 @!@!@
@!@!@STARTMSG 1000:0 @!@!@
The model check run produced error-states - we will generate the SpecTE files now.
@!@!@ENDMSG 1000 @!@!@
@!@!@STARTMSG 1000:0 @!@!@
The file /Users/loki/arbeit/microsoft/dev/tlaplus/runtime-org.lamport.tla.toolbox.product.product.product/QueensPluscal_1579286757638/QueensPluscal.toolbox/FourQueens/SpecTE.tla has been created.
@!@!@ENDMSG 1000 @!@!@
@!@!@STARTMSG 1000:0 @!@!@
The file /Users/loki/arbeit/microsoft/dev/tlaplus/runtime-org.lamport.tla.toolbox.product.product.product/QueensPluscal_1579286757638/QueensPluscal.toolbox/FourQueens/SpecTE.cfg has been created.
@!@!@ENDMSG 1000 @!@!@
@!@!@STARTMSG 2186:0 @!@!@
Finished in 2069ms at (2020-01-28 16:51:32)
@!@!@ENDMSG 2186 @!@!@
---- MODULE SpecTE ----
EXTENDS Sequences, Toolbox, TLC, Naturals

\* 
\*  QueensPluscal follows
\* 

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

CONSTANT N             \** number of queens and size of the board
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
  \A i \in 1 .. Len(queens)-1 : \A j \in (i - 1) .. Len(queens) : 
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
              exts = { Append(queens,q) : q \in cols }
         do
           if (nxtQ = N)
           then todo := todo \ {queens}; sols := sols \union exts;
           else todo := (todo \ {queens}) \union exts;
           end if;
         end with;
       end while;
     end algorithm
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-2ed860b26a15ec8be61ed184eb8c9ae0
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
                            LET exts == { Append(queens,q) : q \in cols } IN
                              IF (nxtQ = N)
                                 THEN /\ todo' = todo \ {queens}
                                      /\ sols' = (sols \union exts)
                                 ELSE /\ todo' = ((todo \ {queens}) \union exts)
                                      /\ sols' = sols
                   /\ pc' = "nxtQ"
              ELSE /\ pc' = "Done"
                   /\ UNCHANGED << todo, sols >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == nxtQ
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-fcc4c3104f960f6e4881fc76793c3cb5

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


\* 
\*  SpecTE follows
\* 


\* CONSTANT definitions @modelParameterConstants:0N
const_158025887640018000 == 
3
----

\* TRACE Sub-Action definition 0
LiveSpec_sa_0 ==
    (
        /\ todo = ({<<>>})
        /\ sols = ({})
        /\ pc = ("nxtQ")
        /\ todo' = ({<<1>>, <<2>>, <<3>>})
        /\ sols' = ({})
        /\ pc' = ("nxtQ")
    )

\* TRACE Sub-Action definition 1
LiveSpec_sa_1 ==
    (
        /\ todo = ({<<1>>, <<2>>, <<3>>})
        /\ sols = ({})
        /\ pc = ("nxtQ")
        /\ todo' = ({<<2>>, <<3>>, <<1, 3>>})
        /\ sols' = ({})
        /\ pc' = ("nxtQ")
    )

\* TRACE Sub-Action definition 2
LiveSpec_sa_2 ==
    (
        /\ todo = ({<<2>>, <<3>>, <<1, 3>>})
        /\ sols = ({})
        /\ pc = ("nxtQ")
        /\ todo' = ({<<3>>, <<1, 3>>})
        /\ sols' = ({})
        /\ pc' = ("nxtQ")
    )

\* TRACE Sub-Action definition 3
LiveSpec_sa_3 ==
    (
        /\ todo = ({<<3>>, <<1, 3>>})
        /\ sols = ({})
        /\ pc = ("nxtQ")
        /\ todo' = ({<<1, 3>>, <<3, 1>>})
        /\ sols' = ({})
        /\ pc' = ("nxtQ")
    )

\* TRACE Sub-Action definition 4
LiveSpec_sa_4 ==
    (
        /\ todo = ({<<1, 3>>, <<3, 1>>})
        /\ sols = ({})
        /\ pc = ("nxtQ")
        /\ todo' = ({<<3, 1>>})
        /\ sols' = ({})
        /\ pc' = ("nxtQ")
    )

\* TRACE Sub-Action definition 5
LiveSpec_sa_5 ==
    (
        /\ todo = ({<<3, 1>>})
        /\ sols = ({})
        /\ pc = ("nxtQ")
        /\ todo' = ({})
        /\ sols' = ({})
        /\ pc' = ("nxtQ")
    )

\* TRACE Action Constraint definition traceExploreActionConstraint
_SpecTEActionConstraint ==
<<
LiveSpec_sa_0,
LiveSpec_sa_1,
LiveSpec_sa_2,
LiveSpec_sa_3,
LiveSpec_sa_4,
LiveSpec_sa_5
>>[TLCGet("level")]
----

def_ov_15802590929252000 == 
<<
([todo |-> {<<>>},sols |-> {},pc |-> "nxtQ"]),
([todo |-> {<<1>>, <<2>>, <<3>>},sols |-> {},pc |-> "nxtQ"]),
([todo |-> {<<2>>, <<3>>, <<1, 3>>},sols |-> {},pc |-> "nxtQ"]),
([todo |-> {<<3>>, <<1, 3>>},sols |-> {},pc |-> "nxtQ"]),
([todo |-> {<<1, 3>>, <<3, 1>>},sols |-> {},pc |-> "nxtQ"]),
([todo |-> {<<3, 1>>},sols |-> {},pc |-> "nxtQ"]),
([todo |-> {},sols |-> {},pc |-> "nxtQ"])
>>
----


\* VARIABLE TraceExp

\* TRACE INIT definition traceExploreInit
_SpecTEInit ==
    /\ todo = (
            {<<>>}
        )
    /\ sols = (
            {}
        )
    /\ pc = (
            "nxtQ"
        )
\*     /\ TraceExp = TRUE

----

\* TRACE NEXT definition traceExploreNext
_SpecTENext ==
/\  \/ LiveSpec_sa_0
    \/ LiveSpec_sa_1
    \/ LiveSpec_sa_2
    \/ LiveSpec_sa_3
    \/ LiveSpec_sa_4
    \/ LiveSpec_sa_5
\* /\ TraceExp' = TraceExp



=============================================================================
\* Modification History
\* Created Tue Jan 28 16:47:56 PST 2020 by loki
