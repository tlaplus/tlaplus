------------------ MODULE testinvalidinvariant --------------------
EXTENDS Integers

VARIABLES x
Init == /\ x = 1
Next == /\ x'= x + 1 
Spec == Init /\ [][Next]_<<x>>

\* Primed variable is invalid.
Invariant == x' \in Nat

==================================================================
