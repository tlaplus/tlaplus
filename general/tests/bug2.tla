--------------- MODULE test -------------


EXTENDS TLC, Integers, Sequences

VARIABLE x

FApply(f, Op(_,_), Identity) ==
  LET fa[S \in SUBSET DOMAIN f] ==
        IF S = { } THEN Print("a", Identity)
                   ELSE LET s == CHOOSE s \in S : TRUE
                        IN Print("b", Op(f[s], fa[S \ {s}]))
  IN  fa[DOMAIN f]


Init == /\ Print("foo", TRUE)
        /\ x = 1
        /\ IF FApply([i \in {"a", "b", "c"} |-> 3], *, 1) = 27
             THEN Print("Test 1 OK", TRUE)
             ELSE Assert(FALSE, "Test 1 Failed")


Next ==  x' = x



Inv ==  TRUE

         

Constraint == TRUE
=========================================
