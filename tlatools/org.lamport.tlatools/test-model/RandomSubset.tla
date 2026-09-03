--------------------------- MODULE RandomSubset ---------------------------
EXTENDS Integers, FiniteSets, Randomization

VARIABLE x, y, z, p, q

Product == (1..200) \X (1..200) \X (1..200)
BigProduct == (1..4000) \X (1..4000) \X (1..4000)

\* p and q draw from a product where TLC generates states, Product having
\* fewer elements than an int holds and BigProduct more.
Init == /\ x \in RandomSubset(1001, 1..100000000)
        /\ y \in RandomSubset(2, 100000000..100000010)
        /\ z = TRUE
        /\ p \in RandomSubset(2, Product)
        /\ q \in RandomSubset(2, BigProduct)

Next == /\ UNCHANGED <<x, y, p, q>>
        /\ z' = FALSE
        

Spec == Init /\ [][Next]_<<x,y,z,p,q>>

Inv == z = TRUE

\* Unlike Inv, never violated, so it reaches every drawn tuple and not only the
\* one that the error trace prints.
TypeOK == /\ x \in 1..100000000
          /\ y \in 100000000..100000010
          /\ z \in BOOLEAN
          /\ p \in Product
          /\ q \in BigProduct

ASSUME Cardinality(RandomSubset(1000, Product)) = 1000
ASSUME RandomSubset(1000, Product) \subseteq Product

ASSUME Cardinality(RandomSubset(1000, BigProduct)) = 1000
ASSUME RandomSubset(1000, BigProduct) \subseteq BigProduct

\* The same products read as sets of functions on 1..3, which a tuple being a
\* function on an interval makes them, so a drawn tuple is one of those.
ASSUME RandomSubset(1000, Product) \subseteq [1..3 -> 1..200]
ASSUME RandomSubset(1000, BigProduct) \subseteq [1..3 -> 1..4000]
=============================================================================
