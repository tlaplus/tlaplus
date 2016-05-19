--------------- MODULE test31  -------------

(* Test replacement of and by infix operators and overridden operators. *)

EXTENDS TLC, Naturals, Sequences

VARIABLE x

CONSTANT P(_,_), _++_ , Plus(_, _), PLen(_)

PlusPlus(a, b) == <<a, b>>

PRep(a, b) == {a, b}

MCSeq(a) = {a}

MCCat(a, b) == a + b

Init == /\ x = 1
        /\ IF P(2, x+3) = {2, 4}
             THEN Print("Test 1 OK", TRUE)
             ELSE Assert(FALSE, "Test 1 Failed")
        /\ IF (2++(x+3)) = <<2, 4>>
             THEN Print("Test 2 OK", TRUE)
             ELSE Assert(FALSE, "Test 2 Failed")
        /\ IF PLen(<<1, 2, 3>>) = 3
             THEN Print("Test 3 OK", TRUE)
             ELSE Assert(FALSE, "Test 3 Failed")
        /\ IF Plus(2, x+3) = 6
             THEN Print("Test 4 OK", TRUE)
             ELSE Assert(FALSE, "Test 4 Failed")
        /\ IF Seq(22) = {22}
             THEN Print("Test 5 OK", TRUE)
             ELSE Assert(FALSE, "Test 5 Failed")
        /\ IF 1 \o 2 = 3                          (* Huh???? *)
             THEN Print("Test 6 OK", TRUE)
             ELSE Assert(FALSE, "Test 6 Failed")
        /\ LET a \prec b == a < b
           IN  IF 1 \prec 2
                 THEN Print("Test 7 OK", TRUE)
                 ELSE Assert(FALSE, "Test 7 Failed")

Next == UNCHANGED x

Inv ==  TRUE

=========================================
