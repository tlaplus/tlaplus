------------------------------ MODULE Peterson ------------------------------ 

(***************************************************************************)
(* This specification describes Peterson's algorithm.  It is a modification *)
(* modification of one found on Wikipedia, written in terms of a single    *)
(* parameterized process, instantiated with parameter self = 0 and 1.      *)
(***************************************************************************)

(***************************************************************************)
(* We define Not(i) to be the process number other than i, so Not(0) = 1   *)
(* and Not(1) = 0.                                                         *)
(***************************************************************************)
Not(i) == IF i = 0 THEN 1 ELSE 0

(*************************************************************************
Here is the algorithm in +Cal (using the C syntax):

--algorithm Peterson {
   variables flag = [i \in {0, 1} |-> FALSE], turn = 0;
   process (proc \in {0,1}) {
     a0: while (TRUE) { 
     a1:   flag[self] := TRUE; 
     a2:   turn := Not(self);       
     a3:   while (flag[Not(self)] /\ turn = Not(self)) {
             skip };
     cs:   skip;  \* critical section   
     a4:   flag[self] := FALSE;            
     } \* end while
    } \* end process
  }
************************************************************************)

(***************************************************************************)
(* Here is the TLA+ translation of the +Cal code, obtained by running pcal *)
(* with the -wf option, which defines Spec to be a specification that      *)
(* assumes weak fairness of the next-state actions of both processes.      *)
(* This fairness assumption is discussed below.                            *)
(***************************************************************************)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9255d446219a56b97b6d3847e8a2c94c
VARIABLES flag, turn, pc

vars == << flag, turn, pc >>

ProcSet == ({0,1})

Init == (* Global variables *)
        /\ flag = [i \in {0, 1} |-> FALSE]
        /\ turn = 0
        /\ pc = [self \in ProcSet |-> "a0"]

a0(self) == /\ pc[self] = "a0"
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << flag, turn >>

a1(self) == /\ pc[self] = "a1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ turn' = turn

a2(self) == /\ pc[self] = "a2"
            /\ turn' = Not(self)
            /\ pc' = [pc EXCEPT ![self] = "a3"]
            /\ flag' = flag

a3(self) == /\ pc[self] = "a3"
            /\ IF flag[Not(self)] /\ turn = Not(self)
                  THEN /\ TRUE
                       /\ pc' = [pc EXCEPT ![self] = "a3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << flag, turn >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ UNCHANGED << flag, turn >>

a4(self) == /\ pc[self] = "a4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a0"]
            /\ turn' = turn

proc(self) == a0(self) \/ a1(self) \/ a2(self) \/ a3(self) \/ cs(self)
                 \/ a4(self)

Next == (\E self \in {0,1}: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-3c75243f0ddf7b933ebf70f115d692f3

(***************************************************************************)
(* Here is the invariant property that the algorithm should satisfy.  It   *)
(* asserts that at least one process is not in its critical section.,      *)
(***************************************************************************)
MutualExclusion == \E i \in {0, 1} : pc[i] # "cs"

(***************************************************************************)
(* It's a good idea to check an algorithm for liveness, to make sure that  *)
(* safety isn't ensured by an error that prevents anything interesting     *)
(* from happening.  Peterson's algorithm is supposed to be starvation      *)
(* free.  The easiest and best way to check that no process is ever        *)
(* starved is to assume that both processes keep trying to enter their     *)
(* critical sections and check that both of them do enter it infinitely    *)
(* often.  This is done by assuming weak fairness of both processes next   *)
(* state actions and checking that the following formula is satisfied.     *)
(***************************************************************************)
InfinitelyOftenInCS == \A i \in {0, 1} : []<>(pc[i] = "cs")

(***************************************************************************)
(* The spec of a starvation free mutual exclusion algorithm asserts that,  *)
(* if any process wants to enter its critical section, then it eventually  *)
(* does.  A process indicates that it wants to enter by leaving its        *)
(* noncritical section.  In this representation of the algorithm, process  *)
(* i is in its noncritical section iff pc[i] = "a0".  It leaves the        *)
(* noncritical section by executing an a0(i) step.  that sets pc[i] to     *)
(* "a1".  So we assume weak fairness of the action proc(i) /\ pc[i] #      *)
(* "a0", the next-state action of process i when it is not in its          *)
(* noncritical section, for each i.  This gives us the spec.               *)
(***************************************************************************)
FairSpec == /\ Init 
            /\ [][Next]_vars 
            /\ \A self \in {0,1}: WF_vars(proc(self) /\ (pc[self] # "a0"))

(***************************************************************************)
(* We check that this spec satisfies the following condition, which        *)
(* asserts that whenever a process i leaves the noncritical section (by    *)
(* setting pc[i] to "a1"), it eventually enters its critical section.      *)
(***************************************************************************)
DeadlockFree == \A i \in {0,1} : (pc[i] = "a1") ~> (pc[i] = "cs") 

-----------------------------------------------------------------------------
(***************************************************************************)
(* To prove mutual exclusion, we find an inductive invariant Inv that is   *)
(* true initially and implies mutual exclusion.  In other words, we must   *)
(* find an Inv that satisfies                                              *)
(*                                                                         *)
(*    THEOREM /\ Init => Inv                                               *)
(*            /\ Inv /\ [Next]_vars => Inv'                                *)
(*            /\ Inv => MutualExclusion                                    *)
(*                                                                         *)
(* The inductive invariant Inv will have the form TypeOK /\ I              *)
(* where TypeOK just asserts type-correctness and I is the interesting     *)
(* part.  For Peterson's algorithm, TypeOK is:                             *)
(***************************************************************************)
TypeOK == /\ pc \in [{0,1} -> {"a0", "a1", "a2", "a3", "cs", "a4"}]
          /\ turn \in {0, 1}
          /\ flag \in [{0,1} -> BOOLEAN]

(***************************************************************************)
(* It turns out that we can use the following I.  (I explain below how I   *)
(* found I.)                                                               *)
(***************************************************************************)
I == \A i \in {0, 1} :
       /\ (pc[i] \in {"a2", "a3", "cs", "a4"} ) => flag[i]
       /\ (pc[i] \in {"cs", "a4"}) => /\ pc[Not(i)] \notin {"cs", "a4"}
                                      /\ (pc[Not(i)] = "a3") => (turn = i)

(***************************************************************************)
(* so we have:                                                             *)
(***************************************************************************)
Inv == TypeOK /\ I

(***************************************************************************)
(* We can easily use TLC to check Init => Inv by checking that Inv is an   *)
(* invariant of the specification.  We can check that Inv satisfies        *)
(*                                                                         *)
(*    Inv /\ [Next]_vars => Inv'                                           *)
(*                                                                         *)
(* by checking that Inv is an invariant of the following specification.    *)
(***************************************************************************)
ISpec == Inv /\ [][Next]_vars

(***************************************************************************)
(* This works only because Inv is written as the conjunction TypeOK and    *)
(* something else, where TypeOK has the form it does.  (Otherwise, TLC     *)
(* would not be able to handle Inv as an initial predicate.)  Moreover, to *)
(* compute the initial states, TLC must calculate all states that satisfy  *)
(* the type-correctness invariant.  For most specs, this is an enormous    *)
(* number of states except perhaps for the tiniest of models, so this      *)
(* seldom works.  However, Peterson's algorithm is so simple that it works *)
(* fine.  In fact, I discovered the invariant I by trial and error, using  *)
(* TLC to discover the problems with I that did not make Inv an invariant  *)
(* of ISpec.                                                               *)
(*                                                                         *)
(* Finally, we can check                                                   *)
(*                                                                         *)
(*    Inv => MutualExclusion                                               *)
(*                                                                         *)
(* by having TLC check that MutualExclusion is an invariant of ISpec.      *)
(***************************************************************************)
=============================================================================
