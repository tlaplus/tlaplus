------------------------ MODULE FingerprintExceptionInit --------------------

EXTENDS Integers

VARIABLE x

Init == x = SUBSET(SUBSET(1..36))
Next == IF {1} \in SUBSET(1..31) THEN x' = SUBSET(SUBSET(1..32)) ELSE x' = 2
Spec == Init /\ [][Next]_x

=============================================================================