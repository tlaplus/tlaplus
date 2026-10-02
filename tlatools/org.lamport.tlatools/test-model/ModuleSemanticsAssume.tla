------------------------ MODULE ModuleSemanticsAssume -----------------------
\* TLC checks each shared proposition as a startup assumption. A false result
\* is a semantic disagreement with ModuleSemanticsTheorems.tla.
EXTENDS TLC, TLCExt

INSTANCE ModuleSemanticsCases

ASSUME BagCardPair
ASSUME BagCupPair
ASSUME BagUnionPair
ASSUME RandomSubsetOne
ASSUME RandomSubsetBelowMaxOne

-----------------------------------------------------------------------------
\* TLAPS proves every proposition below in ModuleSemanticsTheorems.  The
\* refusals are AssertError assumptions: giving up is acceptable, whereas a
\* wrong answer is not.

\* TLC cannot represent the sums beyond MaxInt, so Bags reports an overflow.
ASSUME AssertError("Overflow when computing 2147483647+2147483647", BagCardMax)
ASSUME AssertError("Overflow when computing 2147483647+1", BagCupMax)
ASSUME AssertError("Overflow when computing 2+2147483647", BagUnionMax)

\* No subset has -1 elements, so TLC may refuse RandomSubset(-1, S).
\* Randomization does not check the sign, so the refusal is the message of
\* a NegativeArraySizeException instead of an argument error.
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.Randomization.RandomSubset(tlc2.value.impl.Value,tlc2.value.impl.Value),\nbut it produced the following error:\n-1",
                   RandomSubsetNegRefl)

-----------------------------------------------------------------------------
\* TLC fails on the following although it represents every value involved.
\* They stay commented until it is fixed.

\* EnumerableValue.computeOptimalMandA searches upward from the set's size
\* for the modulus of its random enumeration.  From the prime MaxInt the
\* search wraps to -2^31 and Primes.primeFactors rejects it.
\* ASSUME RandomSubsetMaxOne

-----------------------------------------------------------------------------
\* TLC deliberately deviates from the semantics on the following, so they
\* stay commented.

\* TLC overrides RandomSubset with a Java method that draws a new subset on
\* every evaluation, so the two sides usually differ and TLC rejects this
\* theorem.
\* ASSUME RandomSubsetDet

=============================================================================
