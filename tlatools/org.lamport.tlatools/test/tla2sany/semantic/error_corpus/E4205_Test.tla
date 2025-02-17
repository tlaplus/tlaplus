All built-in operators have level constraints, where their parameters should
not exceed a specific level. While there are many, many test cases that would
trigger this, the most fundamental is simply priming a primed expression.
---- MODULE E4205_Test ----
VARIABLE v
op == v''
====

