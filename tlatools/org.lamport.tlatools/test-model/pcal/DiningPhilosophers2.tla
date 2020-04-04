
-------------------------- MODULE DiningPhilosophers2  ------------------------ 

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
  procedure foo () 
    begin l2 :+ skip;
          e :+ skip;
          l3 :+ skip;
          p4 : skip ;
          return ;
    end procedure

  procedure foo2 ()
     begin foo2begin : skip;
           return;
     end procedure ;

  fair process DummyProcessSet \in -3..0
   begin dp1: skip ;
   end process

  fair process DummySingleProc = -42
    begin dp1: skip ;
    end process;

  fair process Proc \in 1..(N-1)
begin 
l1 : while TRUE
       do      when sem[self] = 1 ;      \* Get right fork.
               sem[self] := 0 ;
       fox :+ when sem[(self-1) % N] = 1 ; \* Get left fork.
            sem[(self-1) % N] := 0 ;
       e  :+ skip ;                       \* Eat
       l3 :+ sem[self] := 1 ;             \* Release right fork.
       l4 :+ sem[(self-1) % N] := 1 ;     \* Release left fork.
      end while ;
end process

process Leader = 0 \* Proc0 = 0
begin
l01 : while TRUE
         do       when sem[N-1] = 1 ;      \* get left fork
                  sem[N-1] := 0 ;
            l2xx : when sem[0] = 1 ;    \* get right fork
                  sem[0] := 0 ;
            exx  : call foo() ; \* eat
            l03 :+ sem[0] := 1 ;         \* release left fork
                   call foo() ; 
            l04 :+ sem[N-1] := 1 ;        \* release right fork
      end while ;
end process

end algorithm

***********************)

\* BEGIN TRANSLATION
\* Label e of procedure foo at line 23 col 16 changed to e_
\* Label l3 of procedure foo at line 24 col 17 changed to l3_
\* Label dp1 of process DummyProcessSet at line 35 col 15 changed to dp1_
VARIABLES sem, pc, stack

vars == << sem, pc, stack >>

ProcSet == (-3..0) \cup {-42} \cup (1..(N-1)) \cup {0}

Init == (* Global variables *)
        /\ sem = [i \in 0..(N-1) |-> 1]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in -3..0 -> "dp1_"
                                        [] self = -42 -> "dp1"
                                        [] self \in 1..(N-1) -> "l1"
                                        [] self = 0 -> "l01"]

l2(self) == /\ pc[self] = "l2"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "e_"]
            /\ UNCHANGED << sem, stack >>

e_(self) == /\ pc[self] = "e_"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l3_"]
            /\ UNCHANGED << sem, stack >>

l3_(self) == /\ pc[self] = "l3_"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "p4"]
             /\ UNCHANGED << sem, stack >>

p4(self) == /\ pc[self] = "p4"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ sem' = sem

foo(self) == l2(self) \/ e_(self) \/ l3_(self) \/ p4(self)

foo2begin(self) == /\ pc[self] = "foo2begin"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ sem' = sem

foo2(self) == foo2begin(self)

dp1_(self) == /\ pc[self] = "dp1_"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << sem, stack >>

DummyProcessSet(self) == dp1_(self)

dp1 == /\ pc[-42] = "dp1"
       /\ TRUE
       /\ pc' = [pc EXCEPT ![-42] = "Done"]
       /\ UNCHANGED << sem, stack >>

DummySingleProc == dp1

l1(self) == /\ pc[self] = "l1"
            /\ sem[self] = 1
            /\ sem' = [sem EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "fox"]
            /\ stack' = stack

fox(self) == /\ pc[self] = "fox"
             /\ sem[(self-1) % N] = 1
             /\ sem' = [sem EXCEPT ![(self-1) % N] = 0]
             /\ pc' = [pc EXCEPT ![self] = "e"]
             /\ stack' = stack

e(self) == /\ pc[self] = "e"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![self] = "l3"]
           /\ UNCHANGED << sem, stack >>

l3(self) == /\ pc[self] = "l3"
            /\ sem' = [sem EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ stack' = stack

l4(self) == /\ pc[self] = "l4"
            /\ sem' = [sem EXCEPT ![(self-1) % N] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ stack' = stack

Proc(self) == l1(self) \/ fox(self) \/ e(self) \/ l3(self) \/ l4(self)

l01 == /\ pc[0] = "l01"
       /\ sem[N-1] = 1
       /\ sem' = [sem EXCEPT ![N-1] = 0]
       /\ pc' = [pc EXCEPT ![0] = "l2xx"]
       /\ stack' = stack

l2xx == /\ pc[0] = "l2xx"
        /\ sem[0] = 1
        /\ sem' = [sem EXCEPT ![0] = 0]
        /\ pc' = [pc EXCEPT ![0] = "exx"]
        /\ stack' = stack

exx == /\ pc[0] = "exx"
       /\ stack' = [stack EXCEPT ![0] = << [ procedure |->  "foo",
                                             pc        |->  "l03" ] >>
                                         \o stack[0]]
       /\ pc' = [pc EXCEPT ![0] = "l2"]
       /\ sem' = sem

l03 == /\ pc[0] = "l03"
       /\ sem' = [sem EXCEPT ![0] = 1]
       /\ stack' = [stack EXCEPT ![0] = << [ procedure |->  "foo",
                                             pc        |->  "l04" ] >>
                                         \o stack[0]]
       /\ pc' = [pc EXCEPT ![0] = "l2"]

l04 == /\ pc[0] = "l04"
       /\ sem' = [sem EXCEPT ![N-1] = 1]
       /\ pc' = [pc EXCEPT ![0] = "l01"]
       /\ stack' = stack

Leader == l01 \/ l2xx \/ exx \/ l03 \/ l04

Next == DummySingleProc \/ Leader
           \/ (\E self \in ProcSet: foo(self) \/ foo2(self))
           \/ (\E self \in -3..0: DummyProcessSet(self))
           \/ (\E self \in 1..(N-1): Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in -3..0 : WF_vars(DummyProcessSet(self))
        /\ WF_vars(DummySingleProc)
        /\ \A self \in 1..(N-1) : /\ WF_vars(Proc(self))
                                  /\ SF_vars(fox(self)) /\ SF_vars(e(self)) /\ SF_vars(l3(self)) /\ SF_vars(l4(self))
        /\ /\ WF_vars(Leader) /\ SF_vars(l03) /\ SF_vars(l04)
           /\ WF_vars(foo(0))
           /\ SF_vars(l2(0)) /\ SF_vars(e_(0)) /\ SF_vars(l3_(0))

\* END TRANSLATION

IsEating(i) == IF i = 0 THEN pc[i] = "e0"
                        ELSE pc[i] = "e"

Invariant == \A i \in 0..(N-1) : ~ (IsEating(i) /\ IsEating((i+1)%N))

StarvationFree == \A i \in 0..(N-1) : []<> IsEating(i) 
=============================================================================
