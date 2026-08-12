----------------------------- MODULE Implied -----------------------------
EXTENDS Naturals

VARIABLE x

Init == x = 0
Next == x < 2 /\ x' = x + 1
Spec == Init /\ [][Next]_x

InitProperty == x \in Nat
ActionProperty == x' \in Nat
Property == InitProperty /\ [][ActionProperty]_x

=============================================================================
