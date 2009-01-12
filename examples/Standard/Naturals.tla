------------------------------ MODULE Naturals ------------------------------ 
LOCAL R == INSTANCE ProtoReals

Nat == R!Nat

a + b == a R!+ b
a - b == a R!- b
a * b == a R!* b
a ^ b == a R!^ b
a \leq b == a R!\leq b
a \geq b == b \leq a
a < b == (a \leq b) /\ (a # b)
a > b == b < a
a .. b == {i \in R!Int : (a \leq i) /\ (i \leq b)}
a \div b == CHOOSE n \in R!Int : \E r \in 0 .. (b-1) : a =  b * n + r
a % b    ==  a  -  b * (a \div b)
=============================================================================
