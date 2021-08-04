--algorithm showBug

process Proc \in 1..2 
variables x=[f1 |-> 1 , f2|->self ];

begin 
start: x.f1:=self;
       assert x.f1 = self;
end process;
    
end algorithm

------------- MODULE bug_05_10_03 ------------
EXTENDS Naturals, TLC, FiniteSets
------------------------------------------
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-b9dcdef1a5e6ce1735b61fe6aacca0f9
VARIABLES pc, x

vars == << pc, x >>

ProcSet == (1..2)

Init == (* Process Proc *)
        /\ x = [self \in 1..2 |-> [f1 |-> 1 , f2|->self ]]
        /\ pc = [self \in ProcSet |-> "start"]

start(self) == /\ pc[self] = "start"
               /\ x' = [x EXCEPT ![self].f1 = self]
               /\ Assert(x'[self].f1 = self, 
                         "Failure of assertion at line 8, column 8.")
               /\ pc' = [pc EXCEPT ![self] = "Done"]

Proc(self) == start(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..2: Proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-50c9ab33ebfd9eb7e6aeb12b5bbb6bd1
==========================================
