--------------------------- MODULE DijkstraMutex ---------------------------
(***************************************************************************)
(* This is a PlusCal version of the first published mutual exclusion       *)
(* algorithm, which appeared in                                            *)
(*                                                                         *)
(*    E. W. Dijkstra: "Solution of a Problem in Concurrent                 *)
(*    Programming Control".  Communications of the ACM 8, 9                *)
(*    (September 1965) page 569.                                           *)
(*                                                                         *)
(* Here is the description of the algorithm as it appeared in that paper.  *)
(* The global variables are declared by                                    *)
(*                                                                         *)
(*   Boolean array b, c[1:N]; integer k                                    *)
(*                                                                         *)
(* The initial values of b[i] and c[i] are true, for each i in 1..N.  The  *)
(* initial value of k can be any integer in 1..N.  The pseudo-code for the *)
(* i-th process, for each i in 1..N, is:                                   *)
(*                                                                         *)
(*   integer j;                                                            *)
(*   Li0: b[i] := false;                                                   *)
(*   Li1: if k # i then                                                    *)
(*   Li2: begin c[i] := true;                                              *)
(*   Li3: if b[k] then k := i;                                             *)
(*        go to Li1                                                        *)
(*        end                                                              *)
(*          else                                                           *)
(*   Li4: begin c[i] := false;                                             *)
(*        for j := 1 step 1 until N do                                     *)
(*          if j # i and not c[j] then go to Li1                           *)
(*        end;                                                             *)
(*        critical section;                                                *)
(*        c[i] := true; b[i] := true;                                      *)
(*        remainder of the cycle in which stopping is allowed;             *)
(*        go to Li0                                                        *)
(*                                                                         *)
(* It appears to me that the "else" preceding label Li4 begins the else    *)
(* clause of the if statement beginning at Li1, and that the code from Li4 *)
(* through the end three lines later should be the body of that else       *)
(* clause.  However, the indentation indicates otherwise.  Moreover, that  *)
(* interpretation produces an incorrect algorithm.  It seems that this     *)
(* "else" actually marks an empty else clause for the if statement at Li1. *)
(* (Perhaps there should have been a semicolon after the "else".)          *)
(***************************************************************************)

EXTENDS Integers

(***************************************************************************)
(* There is no reason why the processes need to be numbered from 1 to N.   *)
(* So, we assume an arbitrary set Proc of process names.                   *)
(***************************************************************************)
CONSTANT Proc 

(*********
Here is the PlusCal version of this algorithm.

 --algorithm Mutex 
 { variables b = [i \in Proc |-> TRUE], c = [i \in Proc |-> TRUE], k \in Proc;
   process (P \in Proc)
     variable temp ;
     { Li0: while (TRUE)
             {      b[self] := FALSE;
               Li1: if (k # self) { Li2: c[self] := TRUE;
                                   Li3a: temp := k;
                                   Li3b: if (b[temp]) { Li3c: k := self } ;
                                   Li3d: goto Li1
                                  };
              Li4a: c[self] := FALSE;
                    temp := Proc \ {self};
              Li4b: while (temp # {})
                     { with (j \in temp) 
                        { temp := temp \ {j};
                          if (~c[j]) { goto Li1 }
                        }
                     };                       
                cs: skip;  \* the critical section
               Li5: c[self] := TRUE;
               Li6: b[self] := TRUE;
               ncs: skip  \* non-critical section ("remainder of cycle")
             }
     }
 }
Notes on the PlusCal version:

1. Label Li3d is required by the translation.  It could be eliminated by
   adding a then clause to the if statement of Li3b and putting the goto 
   in both branches of the if statement.

2. The for loop in section Li4 of the original has been changed to
   a while loop that examines the other processes in an arbitrary
   (nondeterministically chosen) order.  Because temp is set equal
   to the set of all processes other than self, there is no need for
   a test corresponding to the "if j # i" in the original.  Note that
   the process-local variable j has been replaced by the identifier
   j that is local to the with statement.
*********)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES b, c, k, pc, temp

vars == << b, c, k, pc, temp >>

ProcSet == (Proc)

Init == (* Global variables *)
        /\ b = [i \in Proc |-> TRUE]
        /\ c = [i \in Proc |-> TRUE]
        /\ k \in Proc
        (* Process P *)
        /\ temp = [self \in Proc |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in Proc -> "Li0"]

Li0(self) == /\ pc[self] = "Li0"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "Li1"]
             /\ UNCHANGED << c, k, temp >>

Li1(self) == /\ pc[self] = "Li1"
             /\ IF k # self
                   THEN /\ pc' = [pc EXCEPT ![self] = "Li2"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Li4a"]
             /\ UNCHANGED << b, c, k, temp >>

Li2(self) == /\ pc[self] = "Li2"
             /\ c' = [c EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "Li3a"]
             /\ UNCHANGED << b, k, temp >>

Li3a(self) == /\ pc[self] = "Li3a"
              /\ temp' = [temp EXCEPT ![self] = k]
              /\ pc' = [pc EXCEPT ![self] = "Li3b"]
              /\ UNCHANGED << b, c, k >>

Li3b(self) == /\ pc[self] = "Li3b"
              /\ IF b[temp[self]]
                    THEN /\ pc' = [pc EXCEPT ![self] = "Li3c"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Li3d"]
              /\ UNCHANGED << b, c, k, temp >>

Li3c(self) == /\ pc[self] = "Li3c"
              /\ k' = self
              /\ pc' = [pc EXCEPT ![self] = "Li3d"]
              /\ UNCHANGED << b, c, temp >>

Li3d(self) == /\ pc[self] = "Li3d"
              /\ pc' = [pc EXCEPT ![self] = "Li1"]
              /\ UNCHANGED << b, c, k, temp >>

Li4a(self) == /\ pc[self] = "Li4a"
              /\ c' = [c EXCEPT ![self] = FALSE]
              /\ temp' = [temp EXCEPT ![self] = Proc \ {self}]
              /\ pc' = [pc EXCEPT ![self] = "Li4b"]
              /\ UNCHANGED << b, k >>

Li4b(self) == /\ pc[self] = "Li4b"
              /\ IF temp[self] # {}
                    THEN /\ \E j \in temp[self]:
                              /\ temp' = [temp EXCEPT 
                                            ![self] = temp[self] \ {j}]
                              /\ IF ~c[j]
                                    THEN /\ pc' = [pc EXCEPT 
                                                     ![self] = "Li1"]
                                    ELSE /\ pc' = [pc EXCEPT 
                                                     ![self] = "Li4b"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                         /\ UNCHANGED temp
              /\ UNCHANGED << b, c, k >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "Li5"]
            /\ UNCHANGED << b, c, k, temp >>

Li5(self) == /\ pc[self] = "Li5"
             /\ c' = [c EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "Li6"]
             /\ UNCHANGED << b, k, temp >>

Li6(self) == /\ pc[self] = "Li6"
             /\ b' = [b EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << c, k, temp >>

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Li0"]
             /\ UNCHANGED << b, c, k, temp >>

P(self) == Li0(self) \/ Li1(self) \/ Li2(self) \/ Li3a(self) \/ Li3b(self)
              \/ Li3c(self) \/ Li3d(self) \/ Li4a(self) \/ Li4b(self)
              \/ cs(self) \/ Li5(self) \/ Li6(self) \/ ncs(self)

Next == (\E self \in Proc: P(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ \A self \in Proc: WF_vars(P(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

(****************************************************************************
The following formula asserts that no two processes are in their
critcal sections at the same time.  It is the invariant that a mutual
exclusion algorithm should satisfy.  You can have TLC check that the
algorithm is a mutual exclusion algorithm by checking that this formula
is an invariant.


****************************************************************************)
MutualExclusion == \A i, j \in Proc : 
                     (i # j) => ~ /\ pc[i] = "cs"
                                  /\ pc[j] = "cs"
(***************************************************************************)
(* An equivalent way to perform the same test would be to change the       *)
(* statement labeled cs (the critical section) to                          *)
(*                                                                         *)
(*   cs: assert \A j \in Proc \ {self} : pc[j] # "cs"                      *)
(*                                                                         *)
(* You can give this a try.  However, the assert statement requires that   *)
(* the EXTENDS statement also import the standard module TLC, so it should *)
(* read                                                                    *)
(*                                                                         *)
(*    EXTENDS Integers, TLC                                                *)
(***************************************************************************)

-----------------------------------------------------------------------------

(***************************************************************************)
(*                               LIVENESS                                  *)
(*                                                                         *)
(* If you are a sophisticated PlusCal user and know a little temporal      *)
(* logic, you can continue reading about the liveness properties of the    *)
(* algorithm.                                                              *)
(*                                                                         *)
(* Dijkstra's algorithm is "deadlock free", which for a mutual exclusion   *)
(* algorithm means that if some process is trying to enter its critical    *)
(* section, then some process (not necessarily the same one) will          *)
(* eventually enter its critical section.  Since a process begins trying   *)
(* to enter its critical section when it is at the control point labeled   *)
(* Li0, and it is in its critical section when it is at control point cs,  *)
(* the following formula asserts deadlock freedom.                         *)
(***************************************************************************)
DeadlockFree == \A i \in Proc : 
                     (pc[i] = "Li0") ~> (\E j \in Proc : pc[j] = "cs")
(***************************************************************************)
(* Dijkstra's algorithm is deadlock free only under the assumption of      *)
(* fairness of process execution.  The simplest such fairness assumption   *)
(* is weak fairness on each process's next-state action.  This means that  *)
(* no process can halt if it is always possible for that process to take a *)
(* step.  The following statement tells the PlusCal translator to define   *)
(* the specification to assert weak fairness of each process's next-state  *)
(* action.                                                                 *)
(*                                                                         *)
(*     PlusCal options (wf)                                                *)
(*                                                                         *)
(* This statement can occur anywhere in the file--either in a comment or   *)
(* before or after the module.  Because of this statement, the translator  *)
(* has added the necessary fairness conjunct to the definition of Spec.    *)
(* So, you can have the TLC model checker check that the algorithm         *)
(* satisfies property DeadlockFree.                                        *)
(***************************************************************************)

(***************************************************************************)
(* Dijkstra's algorithm is not "starvation free", because it allows some   *)
(* waiting processes to "starve", never entering their critical section    *)
(* while other processes keep entering and leaving their critical          *)
(* sections.  Starvation freedom is asserted by the following formula.     *)
(* You can use TLC to show that the algorithm is not starvation free by    *)
(* producing a counterexample trace.                                       *)
(***************************************************************************)
StarvationFree == \A i \in Proc : 
                     (pc[i] = "Li0") ~> (pc[i] = "cs")

(***************************************************************************)
(* In this algorithm, no process can ever be blocked waiting at an `await' *)
(* statement or a `with (v \in S)' statement with S empty.  Therefore,     *)
(* weak fairness of each process means that each process keeps continually *)
(* trying to enter its critical section, and it exits the critical         *)
(* section.  An important requirement of a mutual exclusion solution, one  *)
(* that rules out many simple solutions, is that a process is allowed to   *)
(* remain forever in its non-critical section.  (There is also no need to  *)
(* require that a process that enters its critical section ever leaves it, *)
(* though without that requirement the definition of starvation freedom    *)
(* must be changed.)                                                       *)
(*                                                                         *)
(* We can allow a process to remain forever in its critical section by     *)
(* replacing the `skip' statement that represents the non-critical section *)
(* with the following statement, which allows the process to loop forever. *)
(*                                                                         *)
(*   ncs: either goto Li0 or goto ncs                                      *)
(*                                                                         *)
(* A more elegant method is to change the fairness requirement to require  *)
(* weak fairness of a process's next-state action only when the process is *)
(* not in its non-critical section.  This is accomplished by taking the    *)
(* following formula LSpec as the algorithm's specification.               *)
(***************************************************************************)
LSpec == Init /\ [][Next]_vars 
           /\ \A self \in Proc: WF_vars((pc[self] # "ncs") /\ P(self))

(***************************************************************************)
(* If we allow a process to remain forever in its non-critical section,    *)
(* then our definition of deadlock freedom is too weak.  Suppose process p *)
(* were in its critical section and process q, trying to enter its         *)
(* critical section, reached Li1.  Formula DeadlockFree would allow a      *)
(* behavior in which process q exited its critical section and remained    *)
(* forever in its non-critical section, but process p looped forever       *)
(* trying to enter its critical section and never succeeding.  To rule out *)
(* this possibility, we must replace the formula                           *)
(*                                                                         *)
(*   pc[i] = "Li0"                                                         *)
(*                                                                         *)
(* in DeadLock free with one asserting that control in process i is        *)
(* anywhere in control points Li0 through Li4b.  It's easier to express    *)
(* this by saying where control in process i is NOT, which we do in the    *)
(* following property.                                                     *)
(***************************************************************************)
DeadlockFreedom == 
    \A i \in Proc : 
      (pc[i] \notin {"Li5", "Li6", "ncs"}) ~> (\E j \in Proc : pc[j] = "cs")
(***************************************************************************)
(* Do you see why it's not necessary to include "cs" in the set of values  *)
(* that pc[i] does not equal?                                              *)
(***************************************************************************)



(***************************************************************************)
(* TLC checked invariant MutualExclusion and property DeadlockFree for     *)
(* three processes in about 2 minutes.  It found 90882 distinct states and *)
(* a reachable state graph of diameter 54.                                 *)
(***************************************************************************)
=============================================================================
\* Modification History
\* Last modified Sat Jan 01 07:50:35 PST 2011 by lamport
\* Created Fri Dec 31 14:14:14 PST 2010 by lamport
