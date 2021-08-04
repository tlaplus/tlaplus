--------------------------- MODULE InnerLabeledIf ---------------------------- 
EXTENDS Sequences, Naturals, TLC

(*   
  --algorithm InnerLabeledIf
    variable x \in 1..4 ;
    begin a : if (x < 3)
                then if (x = 1)
                       then skip ; 
                            b : assert x = 1 
                       else c : assert x = 2
                     end if ;
                else if (x = 3)
                       then skip ; 
                            d : assert x = 3 
                       else e : assert x = 4 ;
                     end if ;
              end if ;
          f : print("made it to end") ;
    end algorithm
*)
                    
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-8d605a76553c67cf0740a3d27b57470b
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x \in 1..4
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF (x < 3)
           THEN /\ IF (x = 1)
                      THEN /\ TRUE
                           /\ pc' = "b"
                      ELSE /\ pc' = "c"
           ELSE /\ IF (x = 3)
                      THEN /\ TRUE
                           /\ pc' = "d"
                      ELSE /\ pc' = "e"
     /\ x' = x

b == /\ pc = "b"
     /\ Assert(x = 1, "Failure of assertion at line 10, column 33.")
     /\ pc' = "f"
     /\ x' = x

c == /\ pc = "c"
     /\ Assert(x = 2, "Failure of assertion at line 11, column 33.")
     /\ pc' = "f"
     /\ x' = x

d == /\ pc = "d"
     /\ Assert(x = 3, "Failure of assertion at line 15, column 33.")
     /\ pc' = "f"
     /\ x' = x

e == /\ pc = "e"
     /\ Assert(x = 4, "Failure of assertion at line 16, column 33.")
     /\ pc' = "f"
     /\ x' = x

f == /\ pc = "f"
     /\ PrintT(("made it to end"))
     /\ pc' = "Done"
     /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b \/ c \/ d \/ e \/ f
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c43944356bde2029519b5137bfd80466


=============================================================================
