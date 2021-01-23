---- CONFIG Github362 ----
INIT Init
NEXT Next
PROPERTY Correct
CONSTANT overloadedConst = 4711
====

---- MODULE Github362 ----

EXTENDS TLC

CONSTANT overloadedConst

VARIABLES overloadedName

\* Github362B.tla contains the definition "overloadedName == x".  It is
\* unrelated to the variable "overloadedName" defined above.
Abstract == INSTANCE Github362B WITH
    x <- "x",
    C <- 42

Init ==
    /\ overloadedName = "fizzbuzz"
    /\ overloadedConst = 4711
    /\ Print(<<"Evaluated initial state in A; overloadedName is: ", overloadedName>>, TRUE)        \* fizzbuzz
    /\ Print(<<"From A's perspective, B's overloadedName is: ", Abstract!overloadedName>>, TRUE)   \* x
    /\ Print(<<"Evaluated initial state in A; overloadedConst is: ", overloadedConst>>, TRUE)      \* 4711
    /\ Print(<<"From A's perspective, B's overloadedConst is: ", Abstract!overloadedConst>>, TRUE) \* 42

Next == UNCHANGED overloadedName

Correct == Abstract!Spec

==================
