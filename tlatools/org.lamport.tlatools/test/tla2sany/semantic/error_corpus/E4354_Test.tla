If a PICK step is a quantified temporal formula, the bound must be constant.
---- MODULE E4354_Test ----
VARIABLE v
THEOREM TRUE
PROOF
<1> PICK x \in v : []v
<1> QED
====

