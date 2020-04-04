------------- MODULE test  --------------
EXTENDS Naturals

VARIABLES x

Init == x \in SUBSET (1..32)
        
Next == x' = 1
=============================================
