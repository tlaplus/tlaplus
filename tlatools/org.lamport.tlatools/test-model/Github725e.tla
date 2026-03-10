---- MODULE Github725e ----
VARIABLE a

---- MODULE Inner725e ----
VARIABLE x
F == x
====

I == INSTANCE Inner725e WITH x <- a

Init == a = 0

Next == UNCHANGED a

\* Prime applied to an INSTANCE access: (I!F)' hits getVar with a SubstInNode
Inv == ENABLED (I!F' = 0)
====
