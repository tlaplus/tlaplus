The @ symbol has special syntactic meaning and cannot be used as an
ordinary declared identifier, so it cannot be bound by CHOOSE.
---- MODULE E4261_Choose_Test ----
op == CHOOSE @ : TRUE
====
