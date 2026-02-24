---- MODULE ConstantRank1TLCEval ----
EXTENDS TLC
CONSTANT x0(_)
VARIABLE x
Init == x = TRUE
Next == x' = (x0({"A"} \union {"B"}) = {"C"})
====
---- CONFIG ConstantRank1TLCEval ----
INIT Init
NEXT Next
CONSTANT x0 <- TLCEval
====