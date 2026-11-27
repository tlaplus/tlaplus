----------------------------- MODULE Github1521 -----------------------------
\* https://github.com/tlaplus/tlaplus/issues/1521
\* @ in [<<x>> EXCEPT ![1] = @'] stands for <<x>>[1], so @' is x'. From
\* (FALSE, <<FALSE>>) the successor is (TRUE, <<TRUE>>), which violates Inv.

VARIABLES x, f

Init == /\ x = FALSE
        /\ f = <<FALSE>>

Next == /\ x' = ~x
        /\ f' = [<<x>> EXCEPT ![1] = @']

Spec == Init /\ [][Next]_<<x, f>>

Inv == x => f[1] = FALSE

=============================================================================
