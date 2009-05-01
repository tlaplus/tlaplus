--------------- MODULE test18 -------------

(* Test of fingerprinting. *)

EXTENDS TLC, Naturals, Sequences

VARIABLE x, y, z, w, u

f == [i \in {1,2}, j \in {3,4} |-> i+j]
g == [p \in {1,2} \X {3,4} |-> p[1] + p[2]]
m == [i \in {3,4} |-> <<i, 7>>]

Init == /\ Print("There should be only one distinct state", TRUE)
        /\ x = [a |-> 1, b |-> 2]
        /\ y = <<3, 4>>
        /\ z = {1, 2, 3}
        /\ w = f
        /\ u = [m EXCEPT ![4] = <<4, 8>>]
        /\ IF y # [i \in {1, 2} |-> IF i = 1 THEN 3 ELSE 4]
             THEN Print("Error in comparing seq and fcn", TRUE)
             ELSE TRUE
        

Inv == /\ TRUE

Next == 
  \/ UNCHANGED <<x, y, z, w, u>>

  \/ /\ x' = [i \in {"a", "b"} |-> IF i = "a" THEN 1 ELSE 2]
     /\ UNCHANGED <<y, z, w, u>>

  \/ /\ y' = [i \in {1, 2} |-> IF i = 1 THEN 3 ELSE 4]
     /\ UNCHANGED <<x, z, w, u>>

  \/ /\ y' = <<3>> \o <<4>>
     /\ UNCHANGED <<x, z, w, u>>  

  \/ /\ y' = [y EXCEPT ![2]=4]
     /\ UNCHANGED <<x, z, w, u>>

  \/ /\ y' = [<<3, 7>> EXCEPT ![2]=4]
     /\ UNCHANGED <<x, z, w, u>>

  \/ /\ y' = <<3>> \o <<4>>
     /\ UNCHANGED <<x, z, w, u>>

  \/ /\ z' = {3, 3, 2, 2, 1}
     /\ UNCHANGED <<x, y, w, u>>

  \/ /\ z' = 1..3
     /\ UNCHANGED <<x, y, w, u>>

  \/ /\ z' = {i - 3 : i \in {4, 5, 6, 4, 5}}
     /\ UNCHANGED <<x, y, w, u>>

  \/ /\ z' = DOMAIN <<"a", "b", 4>>
     /\ UNCHANGED <<x, y, w, u>>

  \/ /\ w' = g
     /\ UNCHANGED <<x, y, z, u>>

  \/ /\ u' = [m EXCEPT ![4][2] = @+1]
     /\ UNCHANGED <<x, y, z, w>>         
=========================================
