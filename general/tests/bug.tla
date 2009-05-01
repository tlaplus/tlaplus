-------- MODULE test -----

EXTENDS Naturals, TLC

VARIABLE x

f[i \in 1..10] == f[i]

Init = x = 1

Next = x'=x

Inv = TRUE

======================
