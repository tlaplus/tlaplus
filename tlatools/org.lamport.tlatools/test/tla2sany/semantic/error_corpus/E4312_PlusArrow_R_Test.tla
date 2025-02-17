Leads-to operator -+-> cannot have an action-level parameter.
This has to be a special-case check since -+-> allows temporal-level parameters.
---- MODULE E4312_PlusArrow_R_Test ----
VARIABLE v
op == v -+-> (v')
====

