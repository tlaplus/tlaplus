---- MODULE PrintTraceException ----
EXTENDS Naturals
VARIABLES x, y

Init == x = 0 /\ y = 0

Next == \/ x < 5 /\ x' = x + 1 /\ y' = y
        \/ y < 5 /\ y' = y + 1 /\ x' = x

\* Violated by the fourth state.
Inv == x < 3

\* %d does not fit the name of a field, which is a string, so printing any state
\* of the error trace throws.
Alias == [_format |-> "%d = %s\n", x |-> x, y |-> y]
====
