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

\* BEGIN TRANSLATION PC-3e98cb139311acc8454991fa59d1dee548d00fc231c9955d092da7f030a84ba8
VARIABLES sem, pc

vars == << sem, pc >>

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

\* END TRANSLATION TPC-5bf70a0cad4e8b2c6490b6daf0e6bafd3f65cc65c178083fad766480ec119b3b

inCS(i) ==  (pc[i] = "cs") 

Invariant == \A i, k \in 1..N : (i # k) => ~ (inCS(i) /\ inCS(k))

Liveness == \A i \in 1..N : []<> inCS(i)
=============================================================================
