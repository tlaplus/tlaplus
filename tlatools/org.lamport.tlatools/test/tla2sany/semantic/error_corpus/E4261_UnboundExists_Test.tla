The @ symbol has special syntactic meaning and cannot be used as an
ordinary declared identifier, so it cannot be bound by \E.
---- MODULE E4261_UnboundExists_Test ----
op == \E @ : TRUE
====
