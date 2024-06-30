---------------------------- MODULE SemaphoreMutex --------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat

(**********************
--algorithm SemaphoreMutex
variables sem = 1 ; 
macro P(s) begin when s > 0 ;
                 s := s - 1 ;
end macro

macro V(s) begin s := s + 1 ;
end macro

process Proc \in 1..N
begin
start : while TRUE
         do enter : P(sem) ;
            cs    : skip ;
            exit  : V(sem) ;
        end while ;
end process
end algorithm


***********************)

\* BEGIN TRANSLATION (chksum(pcal) = "a301f784" /\ chksum(tla) = "b8c844fe")
VARIABLES pc, sem

vars == << pc, sem >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ sem = 1
        /\ pc = [self \in ProcSet |-> "start"]

start(self) == /\ pc[self] = "start"
               /\ pc' = [pc EXCEPT ![self] = "enter"]
               /\ sem' = sem

enter(self) == /\ pc[self] = "enter"
               /\ sem > 0
               /\ sem' = sem - 1
               /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ sem' = sem

exit(self) == /\ pc[self] = "exit"
              /\ sem' = sem + 1
              /\ pc' = [pc EXCEPT ![self] = "start"]

Proc(self) == start(self) \/ enter(self) \/ cs(self) \/ exit(self)

Next == (\E self \in 1..N: Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : SF_vars(Proc(self))

\* END TRANSLATION

inCS(i) ==  (pc[i] = "cs") 

Invariant == \A i, k \in 1..N : (i # k) => ~ (inCS(i) /\ inCS(k))

Liveness == \A i \in 1..N : []<> inCS(i)
=============================================================================
