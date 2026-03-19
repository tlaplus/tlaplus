---------- MODULE Test2a -----------

(* This spec originates from an email conversation between Leslie and Yuan in 2009 *)

EXTENDS Naturals
VARIABLE x

Init == x=0

Next == x' = (x+1)%5

Spec == Init /\ [][Next]_x /\ WF_x(Next)

Prop1 == []<>(x=5)

neg_Prop1 == ~(Prop1)
==============================================
