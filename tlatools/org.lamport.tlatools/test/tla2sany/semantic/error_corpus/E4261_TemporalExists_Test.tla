The @ symbol has special syntactic meaning and cannot be used as an
ordinary declared identifier, so it cannot be bound by \EE.
---- MODULE E4261_TemporalExists_Test ----
op == \EE @ : TRUE
====
