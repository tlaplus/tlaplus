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
					
\* BEGIN TRANSLATION PC-61d88fedad5ab413596f6be26b904f917005f9d871a7ab0fd9946bbd3b0c9cb8
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

\* END TRANSLATION TPC-c7d4c8414b07337a76b0e7a5b583b157a9a1cc2525ac340357d21110be5aaf56


=============================================================================
