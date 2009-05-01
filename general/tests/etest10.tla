--------------- MODULE etest10  -------------

\* Test that TLC doesn't accept x \in Int if x not a number

EXTENDS TLC, Integers

VARIABLE x

Init == /\ x = "a"
        /\ Print("Should report error here", TRUE)
        /\ Print(x \in Int, TRUE)

Next == /\ x'=x
        /\ Print("Test failed--error not reported", TRUE)
=========================================
