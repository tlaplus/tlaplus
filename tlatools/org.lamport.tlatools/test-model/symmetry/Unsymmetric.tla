--------------------------- MODULE Unsymmetric ---------------------------
CONSTANT S
VARIABLE x

Init ==  x \in S

Back == \/ /\ x \in {1,2}
           /\ x' \in S

\* A:
\*
\* A honors S being symmetric. TLC finds and
\* prints the correct counter-example.

tA == CHOOSE a \in S : TRUE

NextA == \/ /\ x \in S
            /\ IF x = tA THEN x' = 1
                         ELSE x' = 2
SpecA == Init /\ [][NextA \/ Back]_x /\ WF_x(NextA \/ Back)

\* B:
\*
\* 'tb' breaks symmetry because it explicitly
\* requires an element in S that is different to
\* another S element. This is exactly opposite
\* to what symmetry represents. Hence, the spec
\* is _not_ symmetric and thus TLC fails to find a 
\* violation/counter-example (TLC finds the 
\* counter-example when S is not declared symmetric.

tB == LET t1 == CHOOSE a \in S : TRUE
      IN  CHOOSE a \in S \ {t1} : TRUE


NextB == \/ /\ x \in S
            /\ IF x = tB THEN x' = 1
                         ELSE x' = 2
SpecB == Init /\ [][NextB \/ Back]_x /\ WF_x(NextB \/ Back)

\* Liveness

Prop == []<>(x = 2)
============================================================================

