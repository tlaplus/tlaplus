---- MODULE Github649 ----
EXTENDS Naturals

VARIABLE clock

RECURSIVE Check(_,_)
Check(c,n) == IF n = 0 THEN c \in BOOLEAN ELSE Check(c, n - 1)

TypeOK == Check(clock,1)

RECURSIVE Flip(_,_,_)
Flip(v, b, n) == IF n = 0 THEN v = ~b ELSE Flip(v, b, n - 1)

Init == Flip(clock, FALSE, 1)  \* The expression Flip(..) does *not* appear in the coverage result. Some of its parameters are covered (invoked),
                               \* but the Flip(..) itself gets skipped over by TLC.  It correctly does not get marked as uncovered.
Next == clock' = ~clock

Constraint ==
    Flip(clock, ~clock, 2)
====