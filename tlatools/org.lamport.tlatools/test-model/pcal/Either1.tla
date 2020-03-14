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

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-af9f3b0389ad56ee237e79295b3205ff
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

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b \/ c \/ d
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-91542970fa29f8acc63f0f9ca8f27be3

=============================================================================
