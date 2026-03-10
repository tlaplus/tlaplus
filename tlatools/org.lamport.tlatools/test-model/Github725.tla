---- MODULE Github725 ----
VARIABLE a

InstantiatedModule == INSTANCE Inner WITH x <- a

Init == a=100

Next == UNCHANGED a

\* check this invariant to exhibit the issue
Inv == ENABLED (InstantiatedModule!F = 0)
====
---- MODULE Inner ----
VARIABLE x
F == x'
====
