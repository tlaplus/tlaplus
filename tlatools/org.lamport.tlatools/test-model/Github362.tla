---- MODULE Github362 ----

EXTENDS TLC

VARIABLES overloadedName

\* Github362B.tla contains the definition "overloadedName == x".  It is
\* unrelated to the variable "overloadedName" defined above.
Abstract == INSTANCE Github362B WITH
    x <- "x"

Init ==
    /\ overloadedName = "fizzbuzz"
    /\ Print(<<"Evaluated initial state in A; overloadedName is: ", overloadedName>>, TRUE)
    /\ Print(<<"From A's perspective, B's overloadedName is: ", Abstract!overloadedName>>, TRUE)

Next == UNCHANGED overloadedName

Correct == Abstract!Spec

==================
