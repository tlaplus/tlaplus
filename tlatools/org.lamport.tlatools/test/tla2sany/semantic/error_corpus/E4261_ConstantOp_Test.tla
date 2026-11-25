The @ symbol has special syntactic meaning and cannot be used as an
ordinary declared identifier, so it cannot be declared as an operator constant.
---- MODULE E4261_ConstantOp_Test ----
CONSTANT @(_)
====
