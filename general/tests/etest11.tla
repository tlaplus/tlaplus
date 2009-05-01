--------------- MODULE etest11  -------------

\* Test that TLC doesn't accept x \in STRING if x not a string

EXTENDS TLC

VARIABLE x

Init == /\ x = 1
        /\ Print("Should report error here", TRUE)
        /\ Print(x \in STRING, TRUE)

Next == /\ x'=x
        /\ Print("Test failed--error not reported", TRUE)
=========================================
