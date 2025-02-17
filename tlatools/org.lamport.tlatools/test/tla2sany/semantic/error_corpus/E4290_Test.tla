Use of the prime operator inside of recursive operators should be prevented,
as it makes it very easy to double-prime an expression.
---- MODULE E4290_Test ----
RECURSIVE op(_)
op(x) == x'
====

