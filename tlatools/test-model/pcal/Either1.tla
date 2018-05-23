------------------------------- MODULE Either1 ------------------------------ 
EXTENDS Naturals, Sequences, TLC

(* --algorithm Either
      variables x = 0 ; y = 0 ;
      begin a: either x := 1 ; b: x := x + 1;
                   or y := 1 ; c: y := y + 1;
               end either ;
            d: assert x+y = 2 ;
     end algorithm
*)

\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ \/ /\ x' = 1
           /\ pc' = "b"
           /\ y' = y
        \/ /\ y' = 1
           /\ pc' = "c"
           /\ x' = x

b == /\ pc = "b"
     /\ x' = x + 1
     /\ pc' = "d"
     /\ y' = y

c == /\ pc = "c"
     /\ y' = y + 1
     /\ pc' = "d"
     /\ x' = x

d == /\ pc = "d"
     /\ Assert(x+y = 2, "Failure of assertion at line 9, column 16.")
     /\ pc' = "Done"
     /\ UNCHANGED << x, y >>

Next == a \/ b \/ c \/ d
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
