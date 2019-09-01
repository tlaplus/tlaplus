------------------------------- MODULE NoLoop ------------------------------- 
EXTENDS Sequences, Naturals, TLC

(*   
  --algorithm NoLoop
    variable x = 0; y = 0 ;
    begin a : with i = 3 do x := i ; end with;
          b : with j \in { 1 , 2 } do y := j ; x := x + y ; end with ;
          c : if y = 1 then x := x + 1 ; else x := x + y; end if;
              when Print ( x , TRUE );
    end algorithm
*)
					
\* BEGIN TRANSLATION PC-c90cc119dbd20411203bd6347a7257fee1e84194f98c495d15bb09f2879fe86a
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
           ELSE /\ x' = x + y
     /\ Print ( x' , TRUE )
     /\ pc' = "Done"
     /\ y' = y

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b \/ c
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION TPC-bbf9d731692384f78544c5c022660889a8e099f70cd621eae123410b4c137123
=============================================================================
