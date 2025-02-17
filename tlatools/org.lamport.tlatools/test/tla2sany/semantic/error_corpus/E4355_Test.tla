Although TLA+ is nominally untyped, there are certain definition categories
that can be checked for compatibility; here, an ASSUME/PROVE definition is
used where an ordinary expression is required, which is an error. The proof
parts of the language can usually reference the non-proof parts, but rarely
vice-versa.
---- MODULE E4355_Test ----
THEOREM thm == ASSUME TRUE PROVE TRUE
op == thm
====

