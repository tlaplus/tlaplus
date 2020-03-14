---- MODULE Github407 ----
Data == {"d1", "d2"}

VARIABLES state

Init == state = {}

Next == \E e \in Data: state' = state \union {e}
=============================================================================
