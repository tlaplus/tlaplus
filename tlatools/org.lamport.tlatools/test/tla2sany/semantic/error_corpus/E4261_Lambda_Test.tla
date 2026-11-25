The @ symbol has special syntactic meaning and cannot be used as an
ordinary declared identifier, so it cannot be a LAMBDA parameter.
---- MODULE E4261_Lambda_Test ----
Foo(Op(_)) == Op(0)
op == Foo(LAMBDA @ : 42)
====
