--------------- MODULE etest9  -------------

\* Test that TLC doesn't accept x \in Nat if x not a number

EXTENDS TLC, Naturals

VARIABLE x

Init == /\ x = "a"
        /\ Print("Should report error here", TRUE)
        /\ Print(x \in Nat, TRUE)

Next == /\ x'=x
        /\ Print("Test failed--error not reported", TRUE)
=========================================
