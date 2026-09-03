------------------------- MODULE RandomSubsetNext -------------------------
EXTENDS Integers, Randomization

VARIABLE x, y

Init == /\ x \in RandomSubset(10, 1..1000)
        /\ y = 0

Product == (1..200) \X (1..200) \X (1..200)

Next == /\ x'\in RandomSubset(10, 1..1000)
        /\ y' = y + 1
        /\ RandomSubset(10, Product) \subseteq Product
        
Spec == Init /\ [][Next]_<<x,y>>

Inv == y < 10
=============================================================================
