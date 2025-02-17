If a PICK step is a quantified temporal formula, the bound must be constant.
---- MODULE E2015_Test ----
VARIABLE v
THEOREM 0
PROOF
<1> PICK x \in v : []0
<1> QED
====

