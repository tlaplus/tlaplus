Leads-to operator ~> cannot have an action-level parameter.
This has to be a special-case check since ~> allows temporal-level parameters.
---- MODULE E2003_LeadsTo_L_Test ----
op == (0') ~> 0
====

