------------------ MODULE CharacterTest -------------------

EXTENDS Sequences, Integers, TLCExt

a == "abcd"
b == [x \in DOMAIN a |-> a[x]]
c == "bcd"
A == "a"[1]

ASSUME a = b
ASSUME DOMAIN a = 1..4
ASSUME a[2] = c[1]
ASSUME (a \o c) = (b \o c)
ASSUME <<A,A>> = "aa"
ASSUME <<A,A>> \in Seq({A})

====

---- CONFIG CharacterTest ----
====