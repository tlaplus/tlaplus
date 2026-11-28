-------------------------- MODULE Github1485HighFanout --------------------------
EXTENDS Naturals

VARIABLE x

Init == x = 0

\* A reservoir fits in a small heap; retaining all million successors does not.
Next == x' \in 1..1000000

=============================================================================
