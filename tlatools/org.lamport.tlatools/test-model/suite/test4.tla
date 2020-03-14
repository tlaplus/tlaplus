--------------- MODULE test4 -------------

(* Test of fingerprinting of sets. *)

EXTENDS Naturals, TLC, Sequences

VARIABLE x, y, z, w

Type == 
  /\ x \in {{1, 2, 3}}
  /\ y \in {{"a", "b", "c"}}
  /\ z \in {[a : {1, 2, 3}, b : {1, 2, 3}, c : {1, 2, 3}]}
  /\ w \in {[{1, 2, 3} -> {1, 2, 3}]}


Init == 
  /\ Print("Should find only one distinct state", TRUE)
  /\ x = {1, 2, 3}
  /\ y = {"a", "b", "c"}
  /\ z = [a : {1, 2, 3}, b : {1, 2, 3}, c : {1, 2, 3}]
  /\ w = [{1, 2, 3} -> {1, 2, 3}]

Inv  == 
  /\ TRUE
  /\ x = {1, 2, 3}
  /\ y = {"a", "b", "c"}
  /\ z = [a : {1, 2, 3}, b : {1, 2, 3}, c : {1, 2, 3}]
  /\ w = [{1, 2, 3} -> {1, 2, 3}]


Next ==
  \/ /\ x' = {3, 3, 2, 1}
     /\ UNCHANGED <<y, z, w>>
     /\ Print("Test 1", TRUE)

  \/ /\ x' = 1..3
     /\ UNCHANGED <<y, z, w>>
     /\ Print("Test 2", TRUE)

  \/ /\ x' = {i \in {5, 4, 3, 3, 2, 2, 1} : i \leq 3}
     /\ UNCHANGED <<y, z, w>>
     /\ Print("Test 2", TRUE)

  \/ /\ x' = {i-3 : i \in 4..6}
     /\ UNCHANGED <<y, z, w>>
     /\ Print("Test 2", TRUE)

  \/ /\ x' = {i-3 : i \in {6, 6, 5, 4, 4, 5, 5}}
     /\ UNCHANGED <<y, z, w>>
     /\ Print("Test 2", TRUE)

  \/ /\ x' = { f[i] : i \in 1..3, f \in [{1,2,3} -> {1,2,3}] }
     /\ UNCHANGED <<y, z, w>>
     /\ Print("Test 3", TRUE)

  \/ /\ y' = DOMAIN [a |-> 1, b |-> 2, c |-> 3]
     /\ UNCHANGED <<x, z, w>>
     /\ Print("Test 4", TRUE)
  \/ /\ z' = [{"a", "b", "c"} -> {1, 2, 3}]
     /\ UNCHANGED <<y, x, w>>
     /\ Print("Test 5", TRUE)

  \/ /\ w' = [{3,1, 2} -> {1, 3, 2}]
     /\ UNCHANGED <<y, x, z>>
     /\ Print("Test 6", TRUE)

  \/ /\ w' = [{3,1, 3, 3, 3, 2} -> {2, 2, 1, 3, 2}]
     /\ UNCHANGED <<y, x, z>>
     /\ Print("Test 6", TRUE)


============================================
