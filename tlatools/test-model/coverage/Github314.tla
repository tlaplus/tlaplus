---- MODULE Github314 ----
EXTENDS Naturals

\* Begin nested (base) module
   ---- MODULE Base ----
   EXTENDS Naturals

   VARIABLES x

   Spec == x = 0 /\ [][(x \in Nat /\ x' = x + 1)]_x
   =====
\* End nested (base) module

VARIABLES x

Spec == x = 0 /\ [][(x \in Nat /\ x' = x + 1)]_x
          
F == INSTANCE Base

MyNat == 0..1
====
