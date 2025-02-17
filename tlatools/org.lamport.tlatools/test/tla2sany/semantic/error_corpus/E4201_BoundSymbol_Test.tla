If a symbol is already defined, its name cannot be re-used as a bound symbol
in a quantifier.
---- MODULE E4201_BoundSymbol_Test ----
VARIABLE x
op == \A x \in {} : TRUE
====

