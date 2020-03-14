--------------- MODULE test28  -------------
\* Some random test

EXTENDS TLC, Naturals, Sequences

VARIABLE x

BdedSeq(S, n) == UNION {[1..i -> S] : i \in 0..n}

Init == /\ x = 2
        /\ x > 1 
        /\ Print("Test 1 OK", TRUE)
        /\ 1..x = {1,2}
        /\ Print("Test 2 OK", TRUE)
        /\ {i + 1 : i \in {x}} = {3}
        /\ Print("Test 3 OK", TRUE)
        /\ {i \in {x} : i = 2} = {2}
        /\ Print("Test 4 OK", TRUE)
        /\ \E i \in {x} : i = 2
        /\ Print("Test 5 OK", TRUE)
        /\ \E i \in 1..x : i < x
        /\ Print("Test 6 OK", TRUE)
        /\ IF BdedSeq({x}, 2) # {<<>>, <<2>>, <<2,2>>}
             THEN Print("Failed Test 7", TRUE)
             ELSE Print("Test 7 OK", TRUE)

Next == UNCHANGED x

Inv ==  TRUE

=========================================
