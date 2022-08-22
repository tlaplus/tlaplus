---- MODULE ConstantOperatorConfiguration ----

CONSTANT F(_)
VARIABLE x

Init == x = 0
Next == x' = F(x)
Inv == x /= 2

====
