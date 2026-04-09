---- MODULE Github725 ----
EXTENDS TLC
VARIABLE a

InstantiatedModule == INSTANCE Inner WITH x <- a

Init == a=100

Next == UNCHANGED a

\* check this invariant to exhibit the issue
Inv == ENABLED (InstantiatedModule!F = 0)

AtHundred == a = 100

Stutter == a' = a

PossibleCounts ==
    LET p == TLCGet("all:named")["s:_possible"][1]
    IN /\ p["AtHundred"] = 2
       /\ p["Stutter"] = 1
====
---- MODULE Inner ----
VARIABLE x
F == x'
====
