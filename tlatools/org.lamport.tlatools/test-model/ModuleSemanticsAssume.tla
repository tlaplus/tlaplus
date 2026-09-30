------------------------ MODULE ModuleSemanticsAssume -----------------------
\* TLC checks each shared proposition as a startup assumption. A false result
\* is a semantic disagreement with ModuleSemanticsTheorems.tla.
EXTENDS TLC, TLCExt

INSTANCE ModuleSemanticsCases

ASSUME BagCardPair
ASSUME BagCupPair
ASSUME BagUnionPair

-----------------------------------------------------------------------------
\* TLAPS proves every proposition below in ModuleSemanticsTheorems.  The
\* refusals are AssertError assumptions: giving up is acceptable, whereas a
\* wrong answer is not.

\* TLC cannot represent the sums beyond MaxInt, so Bags reports an overflow.
ASSUME AssertError("Overflow when computing 2147483647+2147483647", BagCardMax)
ASSUME AssertError("Overflow when computing 2147483647+1", BagCupMax)
ASSUME AssertError("Overflow when computing 2+2147483647", BagUnionMax)

=============================================================================
