------------------------------ MODULE BenchmarkSpec ------------------------------
EXTENDS Integers

VARIABLE x, depth

Init == 
    /\ x = 0 
    /\ depth = 0
Next == 
    /\ x' \in {x+1, x+2}
    /\ depth' = depth + 1

Spec == Init /\ [][Next]_<<x, depth>>

Constraint == depth < 500

Inv == ~(x = 20 /\ depth = 20)

=============================================================================