--------------- MODULE test31  -------------

EXTENDS TLC, Naturals, Sequences, FiniteSets

VARIABLE x, y

Init == /\ Print("This test should generate 3 distinct state", TRUE)
        /\ x = 1
        /\ y = 1

Next == \/ /\ Print("1", TRUE)
           /\ x' \in {1, 2, 3}
           /\ y' = 1
           /\ Print(<<"Generated state", x', y'>>, TRUE)

        \/ UNCHANGED <<x, y>>

Inv ==  TRUE

=========================================
