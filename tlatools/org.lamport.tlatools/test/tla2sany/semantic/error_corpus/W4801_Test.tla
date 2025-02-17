If a symbol is defined then a module is imported using INSTANCE and that
module contains a conflicting symbol, generate a warning since the symbol in
the imported module is ignored in favor of the original definition.
---- MODULE W4801_Test ----
Nat == TRUE
INSTANCE Naturals
====

