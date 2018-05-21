--------------------------- MODULE InnerLabeledIf ---------------------------- 
EXTENDS Sequences, Naturals, TLC

(*   
  --algorithm InnerLabeledIf
    variable x \in 1..4 ;
    begin a : if (x < 3)
                then if (x = 1)
                       then skip ; 
                            b : print << x, "should = 1">> ;
                       else c : print << x, "should = 2">> ;
                     end if ;
                else if (x = 3)
                       then skip ; 
                            d : print << x, "should = 3">> ;
                       else e : print << x, "should = 4">> ;
                     end if ;
              end if ;
          f : print("made it to end") ;
    end algorithm
*)
					
(***** BEGIN TRANSLATION ***)
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
     /\ PrintT(<< x, "should = 1">>)
     /\ pc' = "f"
     /\ x' = x

c == /\ pc = "c"
     /\ PrintT(<< x, "should = 2">>)
     /\ pc' = "f"
     /\ x' = x

d == /\ pc = "d"
     /\ PrintT(<< x, "should = 3">>)
     /\ pc' = "f"
     /\ x' = x

e == /\ pc = "e"
     /\ PrintT(<< x, "should = 4">>)
     /\ pc' = "f"
     /\ x' = x

f == /\ pc = "f"
     /\ PrintT(("made it to end"))
     /\ pc' = "Done"
     /\ x' = x

Next == a \/ b \/ c \/ d \/ e \/ f
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

(***** END TRANSLATION ***)


=============================================================================
