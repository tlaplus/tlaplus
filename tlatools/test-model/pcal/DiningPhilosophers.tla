-------------------------- MODULE DiningPhilosophers ------------------------ 

(***************************************************************************)
(* A simple solution to the Dining Philosophers problem in which processes *)
(* 1 through N-1 pick up their lef then their right forks, and process 0   *)
(* picks them up in the opposite order.                                    *)
(***************************************************************************)

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat

(**********************

--algorithm DiningPhilosophers
  variable sem = [i \in 0..(N-1) |-> 1] ; 

process Proc \in 1..(N-1)
begin 
l1 : while TRUE
       do      when sem[self] = 1 ;      \* Get right fork.
               sem[self] := 0 ;
       l2 : when sem[(self-1) % N] = 1 ; \* Get left fork.
            sem[(self-1) % N] := 0 ;
       e  : skip ;                       \* Eat
       l3 : sem[self] := 1 ;             \* Release right fork.
       l4 : sem[(self-1) % N] := 1 ;     \* Release left fork.
      end while ;
end process

process Proc0 = 0
begin
l01 : while TRUE
         do       when sem[N-1] = 1 ;      \* get left fork
                  sem[N-1] := 0 ;
            l02 : when sem[0] = 1 ;    \* get right fork
                  sem[0] := 0 ;
            e0  : skip ;                 \* eat
            l03 : sem[0] := 1 ;          \* release left fork
            l04 : sem[N-1] := 1 ;        \* release right fork
      end while ;
end process

end algorithm

***********************)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-d34a24305f241c923d0f8daa00682e02
VARIABLES sem, pc

vars == << sem, pc >>

ProcSet == (1..(N-1)) \cup {0}

Init == (* Global variables *)
        /\ sem = [i \in 0..(N-1) |-> 1]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..(N-1) -> "l1"
                                        [] self = 0 -> "l01"]

l1(self) == /\ pc[self] = "l1"
            /\ sem[self] = 1
            /\ sem' = [sem EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "l2"]

l2(self) == /\ pc[self] = "l2"
            /\ sem[(self-1) % N] = 1
            /\ sem' = [sem EXCEPT ![(self-1) % N] = 0]
            /\ pc' = [pc EXCEPT ![self] = "e"]

e(self) == /\ pc[self] = "e"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![self] = "l3"]
           /\ sem' = sem

l3(self) == /\ pc[self] = "l3"
            /\ sem' = [sem EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l4"]

l4(self) == /\ pc[self] = "l4"
            /\ sem' = [sem EXCEPT ![(self-1) % N] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l1"]

Proc(self) == l1(self) \/ l2(self) \/ e(self) \/ l3(self) \/ l4(self)

l01 == /\ pc[0] = "l01"
       /\ sem[N-1] = 1
       /\ sem' = [sem EXCEPT ![N-1] = 0]
       /\ pc' = [pc EXCEPT ![0] = "l02"]

l02 == /\ pc[0] = "l02"
       /\ sem[0] = 1
       /\ sem' = [sem EXCEPT ![0] = 0]
       /\ pc' = [pc EXCEPT ![0] = "e0"]

e0 == /\ pc[0] = "e0"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![0] = "l03"]
      /\ sem' = sem

l03 == /\ pc[0] = "l03"
       /\ sem' = [sem EXCEPT ![0] = 1]
       /\ pc' = [pc EXCEPT ![0] = "l04"]

l04 == /\ pc[0] = "l04"
       /\ sem' = [sem EXCEPT ![N-1] = 1]
       /\ pc' = [pc EXCEPT ![0] = "l01"]

Proc0 == l01 \/ l02 \/ e0 \/ l03 \/ l04

Next == Proc0
           \/ (\E self \in 1..(N-1): Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..(N-1) : SF_vars(Proc(self))
        /\ SF_vars(Proc0)

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ff7acdd47d76382441ae75c392052170

IsEating(i) == IF i = 0 THEN pc[i] = "e0"
                        ELSE pc[i] = "e"

Invariant == \A i \in 0..(N-1) : ~ (IsEating(i) /\ IsEating((i+1)%N))

StarvationFree == \A i \in 0..(N-1) : []<> IsEating(i) 
=============================================================================
