Test that "[self]" subscripts are added to expressions within subscripts.

------------------------- MODULE SubSub ----------------------------
EXTENDS Naturals, TLC

ServerID == {1}
ObjectID == {1}

--------------------------------------------------------------------------
(*********
--algorithm SubSub
  process proc \in 1..3
   variables x = [i \in {"a", "b"} |-> 0] ,
             y = [i \in 5..6 |-> "a"] ,
             z
   begin
     lab : z := 5 ;
           y[z] := "b" ;
           x[y[z]] := 1 ;
           assert x[y[z]] = 1 ;
           assert y[z] = "b"
   end process

end algorithm
*****)

\******** BEGIN TRANSLATION ******** PC-888deeb607b0bd876324a4d8615f73f404ffec1c621599f73910ce671c1eefcc
CONSTANT defaultInitValue
VARIABLES pc, x, y, z

vars == << pc, x, y, z >>

ProcSet == (1..3)

Init == (* Process proc *)
        /\ x = [self \in 1..3 |-> [i \in {"a", "b"} |-> 0]]
        /\ y = [self \in 1..3 |-> [i \in 5..6 |-> "a"]]
        /\ z = [self \in 1..3 |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "lab"]

lab(self) == /\ pc[self] = "lab"
             /\ z' = [z EXCEPT ![self] = 5]
             /\ y' = [y EXCEPT ![self][z'[self]] = "b"]
             /\ x' = [x EXCEPT ![self][y'[self][z'[self]]] = 1]
             /\ Assert(x'[self][y'[self][z'[self]]] = 1, 
                       "Failure of assertion at line 20, column 12.")
             /\ Assert(y'[self][z'[self]] = "b", 
                       "Failure of assertion at line 21, column 12.")
             /\ pc' = [pc EXCEPT ![self] = "Done"]

proc(self) == lab(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..3: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\******** END TRANSLATION ******** TPC-181d0dca3b3446e6692de26042b2f91f77ca0150f5b25ef1b70f0b1292c0d433

--------------------------------------------------------------------------



==========================================================================
