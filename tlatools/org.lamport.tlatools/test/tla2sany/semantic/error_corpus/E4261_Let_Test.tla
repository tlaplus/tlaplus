The @ symbol has special syntactic meaning and cannot be used as an
ordinary declared identifier, so it cannot be defined in a LET.
---- MODULE E4261_Let_Test ----
op == LET @ == 0 IN TRUE
====
