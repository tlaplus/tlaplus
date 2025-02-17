While proof steps that consist of a simple expression can be referenced as
expression using their proof step name (see step <1>c), other non-expression
proof steps cannot be used in that way (see step <1>d).
---- MODULE E4351_Test ----
op(x) == x
THEOREM TRUE
PROOF
<1>a TRUE
<1>b HAVE TRUE
<1>c op(<1>a)
<1>d op(<1>b)
<1> QED
====

