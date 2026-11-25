The @ symbol has special syntactic meaning and cannot be used as an
ordinary declared identifier, so it cannot be bound by \AA.
---- MODULE E4261_TemporalForall_Test ----
op == \AA @ : TRUE
====
