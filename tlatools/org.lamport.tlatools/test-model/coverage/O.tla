------------------------------ MODULE O ------------------------------
EXTENDS Naturals

\* Begin nested (inner) module
   ---- MODULE Inner ----
   EXTENDS Naturals

   VARIABLES y

   Step == /\ y < 3
           /\ y' = y + 1

   Bound == y <= 3
   =====
\* End nested (inner) module

VARIABLES x

(* One instantiation reached from both the next-state relation and the       *)
(* invariant. The expression substituted for y is counted separately for     *)
(* each of them, even though they share the Subst of the semantic graph.     *)
I == INSTANCE Inner WITH y <- x

Init == x = 0

Next == I!Step

Inv == I!Bound

Spec == Init /\ [][Next]_x

============
