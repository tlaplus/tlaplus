---------------------------- MODULE test37 -----------------------------

(* Test of standard FiniteSets module *)

EXTENDS FiniteSets, TLC

VARIABLES x

Init == x = 0
Next == x'=x
Inv  ==
       /\ IF IsFiniteSet({"a", "b"})
            THEN Print("Test 1 OK", TRUE)
            ELSE Assert(FALSE, "Test 1 Failed")

       /\ IF IsFiniteSet({})
            THEN Print("Test 2 OK", TRUE)
            ELSE Assert(FALSE, "Test 2 Failed")

       /\ IF Cardinality({}) = 0
            THEN Print("Test 3 OK", TRUE)
            ELSE Assert(FALSE, "Test 3 Failed")

       /\ IF Cardinality({"a", "b"}) = 2
            THEN Print("Test 4 OK", TRUE)
            ELSE Assert(FALSE, "Test 4 Failed")


=============================================================================
