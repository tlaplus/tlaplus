--------------- MODULE test29  -------------

\* Testing proper evaluation of primed variables in action

EXTENDS TLC, Naturals, Sequences

VARIABLE x


Init == x = 2

Next == /\ x' = 2
        /\ x' > 1 
        /\ Print("Test 1 OK", TRUE)
        /\ 1..x' = {1,2}
        /\ Print("Test 2 OK", TRUE)
        /\ {i + 1 : i \in {x'}} = {3}
        /\ Print("Test 3 OK", TRUE)
        /\ {i \in {x'} : i = 2} = {2}
        /\ Print("Test 4 OK", TRUE)
        /\ \E i \in {x'} : i = 2
        /\ Print("Test 5 OK", TRUE)
        /\ \E i \in 1..x' : i < x'
        /\ Print("Test 6 OK", TRUE)



Inv ==  TRUE

=========================================
