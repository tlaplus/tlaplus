Bug: Currently putting an extra `self' subscript in assignment to
     `stack'.



----------- MODULE StackTest -----------
EXTENDS Sequences, Naturals, TLC

(***************************************************************************
--algorithm StackAndPCTest
   procedure P(a=42)
      begin P1: stack[self][1].a := stack[self][1].a + 1;
                assert Head(stack[self]).a = 43 ;
                assert pc[self] = "P1" ;
            P2: return
      end procedure
   process Q \in 0..2
     begin Q1: assert \A i \in ProcSet : pc[i] \in {"P1", "P2", "Q1", "Done"};
               call P(22) ;
     end process;
   end algorithm
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES pc, stack, a

vars == << pc, stack, a >>

ProcSet == (0..2)

Init == (* Procedure P *)
        /\ a = [ self \in ProcSet |-> 42]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Q1"]

P1(self) == /\ pc[self] = "P1"
            /\ stack' = [stack EXCEPT ![self][self][1].a = stack[self][1].a + 1]
            /\ Assert(Head(stack'[self]).a = 43, 
                      "Failure of assertion at line 13, column 17.")
            /\ Assert(pc[self] = "P1", 
                      "Failure of assertion at line 14, column 17.")
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ a' = a

P2(self) == /\ pc[self] = "P2"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ a' = [a EXCEPT ![self] = Head(stack[self]).a]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]

P(self) == P1(self) \/ P2(self)

Q1(self) == /\ pc[self] = "Q1"
            /\ Assert(\A i \in ProcSet : pc[i] \in {"P1", "P2", "Q1", "Done"}, 
                      "Failure of assertion at line 18, column 16.")
            /\ /\ a' = [a EXCEPT ![self] = 22]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "P",
                                                        pc        |->  "Done",
                                                        a         |->  a[self] ] >>
                                                    \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "P1"]

Q(self) == Q1(self)

Next == (\E self \in ProcSet: P(self))
           \/ (\E self \in 0..2: Q(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
========================================
