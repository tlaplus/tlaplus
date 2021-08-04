------------------------------- MODULE NoLoop2 ------------------------------- 
EXTENDS Naturals, TLC

(*   

  --algorithm NoLoop2
    variable x = 0; y = 0 ;
    begin a : with i = 3 do x := i ; end with;
          b : with j \in { 1 , 2 } do y := j ; x := x + y ; end with;
          c : if y = 1 then x := x + 1 ; d : x := 2 * x ;
                       else x := x + y ; end if;
          e : when Print ( x , TRUE );
    end algorithm
   \* should print out 10 or 7

*)
                    
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a111e49229d06e75e660ee8777442285
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ LET i == 3 IN
          x' = i
     /\ pc' = "b"
     /\ y' = y

b == /\ pc = "b"
     /\ \E j \in { 1 , 2 }:
          /\ y' = j
          /\ x' = x + y'
     /\ pc' = "c"

c == /\ pc = "c"
     /\ IF y = 1
           THEN /\ x' = x + 1
                /\ pc' = "d"
           ELSE /\ x' = x + y
                /\ pc' = "e"
     /\ y' = y

d == /\ pc = "d"
     /\ x' = 2 * x
     /\ pc' = "e"
     /\ y' = y

e == /\ pc = "e"
     /\ Print ( x , TRUE )
     /\ pc' = "Done"
     /\ UNCHANGED << x, y >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b \/ c \/ d \/ e
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-7bfbfdcfed4c1aea23c410420c1f4f9d
=============================================================================
