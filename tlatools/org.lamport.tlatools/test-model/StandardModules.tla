------------------------------- MODULE StandardModules -------------------------------
EXTENDS Bags, Sequences, FiniteSets, TLC, RealTime, Naturals, Integers, Randomization
VARIABLES x
Init == FALSE /\ x = 0
Next == [][FALSE /\ x' = x]_<<x>>
============================================================================
