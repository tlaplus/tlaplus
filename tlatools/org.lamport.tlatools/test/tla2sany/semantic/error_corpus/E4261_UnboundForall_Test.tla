The @ symbol has special syntactic meaning and cannot be used as an
ordinary declared identifier, so it cannot be bound by \A.
---- MODULE E4261_UnboundForall_Test ----
op == \A @ : TRUE
====
