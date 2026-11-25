The @ symbol has special syntactic meaning and cannot be used as an
ordinary declared identifier, so it cannot be bound by a bounded CHOOSE.
---- MODULE E4261_ChooseIn_Test ----
op == CHOOSE @ \in {0} : TRUE
====
