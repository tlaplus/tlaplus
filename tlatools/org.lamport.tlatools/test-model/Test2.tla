---------- MODULE Test2 -----------

(* This spec originates from an email conversation between Leslie and Yuan in 2009 *)

EXTENDS Naturals, TLC
VARIABLE x

Init == x=0 /\ TLCSet(42, 0)

Next == x' = (x+1)%5 /\ TLCSet(42, TLCGet(42)+1)

Spec == Init /\ [][Next]_x /\ WF_x(Next)

Prop1 == []<>(x=1)

PostCondition ==
    TLCGet(42) \in {1050, 2000}

PostConditionViolated ==
    TLCGet(42) = 0

==============================================
