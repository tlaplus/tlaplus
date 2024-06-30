----------------------------- MODULE NoParams ------------------------------ 
EXTENDS Sequences, Naturals, TLC

(*   

--algorithm NoParams
    variables sum = 0 ;
    procedure Sum() 
      begin s1: sum := sum + 1;
                return;
      end procedure;
    begin m1 : call Sum();
          m2 : call Sum();
          m3 : when Print(sum, TRUE) ;
   end algorithm 


*)
                    
\* BEGIN TRANSLATION (chksum(pcal) = "3063a211" /\ chksum(tla) = "c3deb76f")
VARIABLES pc, sum, stack

vars == << pc, sum, stack >>

Init == (* Global variables *)
        /\ sum = 0
        /\ stack = << >>
        /\ pc = "m1"

s1 == /\ pc = "s1"
      /\ sum' = sum + 1
      /\ pc' = Head(stack).pc
      /\ stack' = Tail(stack)

Sum == s1

m1 == /\ pc = "m1"
      /\ stack' = << [ procedure |->  "Sum",
                       pc        |->  "m2" ] >>
                   \o stack
      /\ pc' = "s1"
      /\ sum' = sum

m2 == /\ pc = "m2"
      /\ stack' = << [ procedure |->  "Sum",
                       pc        |->  "m3" ] >>
                   \o stack
      /\ pc' = "s1"
      /\ sum' = sum

m3 == /\ pc = "m3"
      /\ Print(sum, TRUE)
      /\ pc' = "Done"
      /\ UNCHANGED << sum, stack >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Sum \/ m1 \/ m2 \/ m3
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
