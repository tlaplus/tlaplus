Proofs cannot occur in between the declaration of a recursive operator and
its definition.
---- MODULE E2032_Proof_Test ----
RECURSIVE op
THEOREM TRUE
PROOF OBVIOUS
op == 0
====

