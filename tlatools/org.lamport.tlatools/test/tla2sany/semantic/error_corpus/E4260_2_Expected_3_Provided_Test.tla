Similar to an operator, a function has a defined number of parameters and if
the wrong number are provided then that should be an error. Unlike operators
a function does constitute a value in itself so only certain misuses of it
can be statically detected. Another difficulty is that multi-parameter
functions can always be called using a single multi-value tuple argument.
---- MODULE E4260_2_Expected_3_Provided_Test ----
f[x \in {}, y \in {}] == 0
op == f[0, 0, 0]
====

