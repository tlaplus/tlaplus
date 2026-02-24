---- MODULE ConstantRank2AssertError ----
EXTENDS TLCExt
CONSTANT x0(_, _)
VARIABLE x
Init == x = TRUE
Next == x' = x0("no error", TRUE)
====
---- CONFIG ConstantRank2AssertError ----
INIT Init
NEXT Next
CONSTANT x0 <- AssertError
====
