---------------------- MODULE test25 ----------------------

(* test of fingerprinting elements of [S -> [B -> C]]  *)

EXTENDS Naturals, Sequences, TLC

CONSTANT S, T, s1, t1, c

VARIABLES x, y, z, w

Init ==  /\ Print("Should find only one state", TRUE)
         /\ x = [i \in 1..3 |-> [j \in {4,5} |-> i+j]]
         /\ y = [a |-> <<"b", "c">>, b |-> <<"c", "d", "e">>]
         /\ z = [i \in S |-> [j \in {2,3} |-> j+1]]
         /\ w = [i \in S |-> [j \in T |-> c]]

Inv == TRUE

Next == 
  \/ UNCHANGED <<x, y, z, w>>

  \/ /\ x' = << [j \in {4,5} |-> 1+j], [j \in {4,5} |-> 2+j], [j \in {4,5} |-> 3+j]>>
     /\ y' = [i \in {"a", "b"} |->
               IF i = "a" THEN [j \in {1,2} |-> IF j = 1 THEN "b" ELSE "c"]
                          ELSE [<<"x", "d", "e">> EXCEPT ![1]= "c"]]
     /\ z' = [[z EXCEPT ![s1] = [@ EXCEPT ![3] = 77]] EXCEPT ![s1][3] = 4]
     /\ w' = [[w EXCEPT ![s1][t1] = s1] EXCEPT ![s1][t1] = c]
      

===========================================================
