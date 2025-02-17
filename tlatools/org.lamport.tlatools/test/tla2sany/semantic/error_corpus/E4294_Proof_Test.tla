Proofs cannot occur in between the declaration of a recursive operator and
its definition.
---- MODULE E4294_Proof_Test ----
RECURSIVE op
THEOREM TRUE
PROOF OBVIOUS
op == 0
====

