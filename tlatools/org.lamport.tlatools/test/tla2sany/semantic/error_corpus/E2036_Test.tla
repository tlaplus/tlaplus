The @ symbol is used to refer to the previous function value when writing a
[f EXCEPT ![x] = @ + 1] function-except expression. Its use outside of that
context should generate an error.
---- MODULE E2036_Test ----
op == @
====

