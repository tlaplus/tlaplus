------------------ MODULE Github696b -------------------
EXTENDS Integers, TLCExt

VARIABLE v

Init == /\ v = {TLCModelValue("A_a"), TLCModelValue("B_a")}
 
Next == UNCHANGED v

Inv == TLCModelValue("B_a") \in v

=======================================================
