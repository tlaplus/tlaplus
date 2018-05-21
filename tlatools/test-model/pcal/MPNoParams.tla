----------------------------- MODULE MPNoParams ------------------------------ 
EXTENDS Sequences, Naturals, TLC

(*   
--algorithm MPNoParams
    variables sum = 0; done = FALSE;

    procedure Sum ()
      begin s1: sum := sum + 1;
                return;
      end procedure;
    process P1 = 1 
    begin p1 : call Sum();
          p2 : done := TRUE ;
    end process 
    process P2 \in 2..4 
     begin
          q1 : call Sum();
          q2 : when done ;
               print sum ;
   end process 
   end algorithm


*)
					
(***** BEGIN TRANSLATION ***)
VARIABLES sum, done, pc, stack

vars == << sum, done, pc, stack >>

ProcSet == {1} \cup (2..4)

Init == (* Global variables *)
        /\ sum = 0
        /\ done = FALSE
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "p1"
                                        [] self \in 2..4 -> "q1"]

s1(self) == /\ pc[self] = "s1"
            /\ sum' = sum + 1
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ done' = done

Sum(self) == s1(self)

p1 == /\ pc[1] = "p1"
      /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "Sum",
                                            pc        |->  "p2" ] >>
                                        \o stack[1]]
      /\ pc' = [pc EXCEPT ![1] = "s1"]
      /\ UNCHANGED << sum, done >>

p2 == /\ pc[1] = "p2"
      /\ done' = TRUE
      /\ pc' = [pc EXCEPT ![1] = "Done"]
      /\ UNCHANGED << sum, stack >>

P1 == p1 \/ p2

q1(self) == /\ pc[self] = "q1"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Sum",
                                                     pc        |->  "q2" ] >>
                                                 \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << sum, done >>

q2(self) == /\ pc[self] = "q2"
            /\ done
            /\ PrintT(sum)
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << sum, done, stack >>

P2(self) == q1(self) \/ q2(self)

Next == P1
           \/ (\E self \in ProcSet: Sum(self))
           \/ (\E self \in 2..4: P2(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(P1) /\ WF_vars(Sum(1))
        /\ \A self \in 2..4 : WF_vars(P2(self)) /\ WF_vars(Sum(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

(***** END TRANSLATION ***)


=============================================================================
