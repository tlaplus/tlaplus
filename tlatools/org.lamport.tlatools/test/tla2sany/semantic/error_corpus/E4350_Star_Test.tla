While proof steps with explicit level can have names, proof steps with
implicit level (like <*> and <+>) cannot.
---- MODULE E4350_Star_Test ----
THEOREM TRUE
PROOF
<*>a. QED
====

