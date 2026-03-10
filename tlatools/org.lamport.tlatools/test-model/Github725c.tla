---- MODULE Github725c ----
VARIABLE a

I == INSTANCE Inner725c WITH x <- a

Init == a = 0

Next == UNCHANGED a

Inv == ENABLED (I!F \in {0, 1, 2})
====
---- MODULE Inner725c ----
VARIABLE x
F == x'
====
