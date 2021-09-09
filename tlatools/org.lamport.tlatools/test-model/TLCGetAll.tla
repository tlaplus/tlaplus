--------------------------- MODULE TLCGetAll -----------------------------
\* Contrary to the hyperproperties tested by DieHardTLA, this test checks that
\* basic hyperproperties work even with multiple TLC workers.  While this is not
\* transparent, it is easy enough for users to aggregate the results of multiple
\* TLC workers as they see fit.
EXTENDS Naturals, TLC, FiniteSets, Sequences

R == 23

ASSUME TLCSet(R, 0)
\* Add a second value to TLCSet that is not changed by Init/Next.
ASSUME TLCSet(42, 0)

VARIABLE x, y

Init ==
    /\ x = 0
    /\ y = 0

Next ==
    \* If TLCSet would be moved below the other two conjuncts, TLCGet(R) in
    \* Postcondition would evaluate to 10100.  This is because of TLC's
    \* left-to-right expression evaluation.
    /\ TLCSet(R, TLCGet(R) + 1)
    /\ x' \in 1..10
    /\ y' \in 1..10

--------------------------------------------------------------------------------

Sum(seq) ==
    \* Some might prefer folds here--me don't.
    LET S[n \in 1..Len(seq)] ==
            IF n = 1
            THEN seq[n]
            ELSE seq[n] + S[n - 1]
    IN S[Len(seq)]

PostCondition ==
    LET vals == TLCGet("all")
    IN /\ DOMAIN vals = {R, 42} 
       \* vars[R] is a tuple with length N where N is the number of workers.
       \* In other words, vars[R] has the value of TLCGet(R) for each worker.
       /\ Len(vals[R]) = TLCGet("config").worker
       \* What is counted explicitly with TLCGet/Set are the number of distinct
       \* states.
       /\ Sum(vals[R]) = TLCGet("distinct")
================================================================================

--------------------------- CONFIG TLCGetAll -----------------------------
INIT Init
NEXT Next
POSTCONDITION PostCondition
================================================================================