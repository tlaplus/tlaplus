------------------------ MODULE ModuleSemanticsAssume -----------------------
\* TLC checks each shared proposition as a startup assumption. A false result
\* is a semantic disagreement with ModuleSemanticsTheorems.tla.
EXTENDS TLC

INSTANCE ModuleSemanticsCases

ASSUME BagCardPair
ASSUME BagCupPair
ASSUME BagUnionPair

-----------------------------------------------------------------------------
\* TLAPS proves every proposition below in ModuleSemanticsTheorems.
\* Bags adds counts in unchecked int arithmetic, so TLC answers FALSE:
\* BagCardinality wraps to -2, and the counts of 1 wrap to MinInt and
\* -2147483647.
\* ASSUME BagCardMax
\* ASSUME BagCupMax
\* ASSUME BagUnionMax

=============================================================================
