----- MODULE Github297 -----
VARIABLE x
INSTANCE B WITH y <- x
Init == x = { }
Next == UNCHANGED vars
====

---- MODULE B ----
VARIABLE y
vars == y
====

---- CONFIG Github297 ----
INIT Init
NEXT Next
=====