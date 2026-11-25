Prime accepts an argument of at most variable level. When @ already stands
for an action, because the function contains a prime, priming it again
exceeds that constraint.
---- MODULE E4205_At_Test ----
VARIABLE v
a[x \in {1}] == v'
op == [a EXCEPT ![1] = @']
====
