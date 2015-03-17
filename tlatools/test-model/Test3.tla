---------- MODULE Test3 -----------

(* This spec originates from an email conversation between Leslie and Yuan in 2009 *)

EXTENDS Naturals
VARIABLE x

Init == x=0

Next == IF x=0 THEN x' \in {1, 2}
        ELSE x' = 0

Spec == Init /\ [][Next]_x /\ WF_x(Next)

Prop1 ==  <>[](x#1) \/ <>[](x#2)
===================================
