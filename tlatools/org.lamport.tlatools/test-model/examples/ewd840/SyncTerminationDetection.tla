---------------------- MODULE SyncTerminationDetection ----------------------
(***************************************************************************)
(* This module contains an abstract specification of the termination       *)
(* detection problem in a ring with synchronous communication. We will     *)
(* prove that the EWD840 algorithm refines this specification.             *)
(***************************************************************************)
EXTENDS Naturals
CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node == 0 .. N-1

VARIABLES 
  active,               \* activation status of nodes
  terminationDetected   \* has termination been detected?

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ terminationDetected \in BOOLEAN

terminated == \A n \in Node : ~ active[n]

(***************************************************************************)
(* Initial condition: the nodes can be active or inactive, termination     *)
(* may (but need not) be detected immediately if all nodes are inactive.   *)
(***************************************************************************)
Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ terminationDetected \in {FALSE, terminated}

Terminate(i) ==  \* node i terminates
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
     (* possibly (but not necessarily) detect termination if all nodes are inactive *)
  /\ terminationDetected' \in {terminationDetected, terminated'}

Wakeup(i,j) ==  \* node i activates node j
  /\ active[i]
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ UNCHANGED terminationDetected

DetectTermination ==
  /\ terminated
  /\ terminationDetected' = TRUE
  /\ UNCHANGED active

Next ==
  \/ \E i \in Node : Terminate(i)
  \/ \E i,j \in Node : Wakeup(i,j)
  \/ DetectTermination

vars == <<active, terminationDetected>>
Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

------------------------------------------------------------------------------
(* Correctness properties *)

TDCorrect == terminationDetected => terminated

Quiescence == [](terminated => []terminated)

Liveness == terminated ~> terminationDetected

=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by merz
