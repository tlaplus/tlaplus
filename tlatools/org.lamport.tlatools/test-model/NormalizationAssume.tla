------------------------- MODULE NormalizationAssume -------------------------
\* TLC normalizes a set enumeration, and the domain of a function or record,
\* only when it has to, e.g. to fingerprint, compare, or enumerate the value.
\* Normalizing compares the elements, so TLC evaluates an expression whose
\* elements it cannot compare, as long as the expression doesn't need the
\* comparison. NormalizationTheorems.tla proves the shared propositions.
EXTENDS Integers, Sequences, FiniteSets, TLC, TLCExt

INSTANCE NormalizationCases WITH TypedA <- TLCModelValue("A_a"),
                                 TypedB <- TLCModelValue("B_a")

\* TLC evaluates these, because it doesn't have to compare the elements.
ASSUME MixedMember
ASSUME MixedFcnApply
ASSUME MixedFcnExcept
ASSUME MixedCupEmptyMember
ASSUME FiniteMixed

\* A typed model value is comparable only with model values of the same type.
ASSUME TypedMember
ASSUME TypedIntMember
ASSUME TypedStringMember
ASSUME IntTypedMember

ASSUME MixedBoundMember

\* Caching the value sorts it, but not its elements.
ASSUME LazyFcnExceptDomain
ASSUME LazyFcnInTuple
ASSUME LazyPredFcnSetNeqEmpty
ASSUME LazyPredSubsetNeqEmpty

ASSUME TupleApplyMixed
ASSUME HeadMixed
ASSUME TailMixed
ASSUME AppendMixed
ASSUME ConcatMixed
ASSUME SubSeqMixed
ASSUME RcdFieldMixed
ASSUME RcdDomainMixed

ASSUME TupleEnumMember
ASSUME RcdEnumMember
ASSUME FcnEnumMember
ASSUME SetEnumMember

ASSUME SubsetMixedMember
ASSUME SubsetMixedCupMember
ASSUME SeqMixedMember
ASSUME ProductMixedMember
ASSUME ProductEmptyRight
ASSUME ProductEmptyLeft
ASSUME ProductEmptyEq
ASSUME FcnSetMixedMember
ASSUME RcdSetMixedMember

\* Membership checks the elements of the enumeration in order, so whether TLC
\* evaluates it depends on the order.
ASSUME AssertError("Attempted to check equality of integer 1 with non-integer:\n\"a\"",
                   MixedMemberSecond)

\* TLC fails to evaluate these, because it compares the elements.
ASSUME AssertError("Attempted to compare string \"a\" with non-string:\n1",
                   MixedPredMember)
ASSUME AssertError("Attempted to check equality of integer 1 with non-integer:\n\"a\"",
                   MixedCapMember)
ASSUME AssertError("Attempted to check equality of integer 2 with non-integer:\n\"a\"",
                   MixedDiffMember)
ASSUME AssertError("Attempted to check equality of string \"a\" with non-string:\n2",
                   MixedCupMember)
ASSUME AssertError("Attempted to check equality of integer 1 with non-integer:\n\"a\"",
                   UnionMixedMember)
ASSUME AssertError("Attempted to check equality of integer 1 with non-integer:\n\"a\"",
                   UnionMixedSingleton)
ASSUME AssertError("Attempted to compare string \"a\" with non-string:\n1",
                   MixedSubseteq)
ASSUME AssertError("Attempted to compare string \"a\" with non-string:\n1",
                   MixedNeqEmpty)
ASSUME AssertError("Attempted to compare string \"a\" with non-string:\n1",
                   EmptyNeqMixed)
ASSUME AssertError("Attempted to compare string \"a\" with non-string:\n1",
                   FcnRangeMixedNeqEmpty)
ASSUME AssertError("Attempted to compare string \"a\" with non-string:\n1",
                   MixedDomainMember)
ASSUME AssertError("Attempted to compare string \"a\" with non-string:\n1",
                   MixedFcnEq)
ASSUME AssertError("Attempted to compare string \"a\" with non-string:\n1",
                   MixedFcnSetMember)
ASSUME AssertError("Attempted to check equality of integer 1 with non-integer:\n\"a\"",
                   SeqMixedPairMember)
ASSUME AssertError("Attempted to compare string \"a\" with non-string:\n1",
                   ProductEmptyNonTuple)
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.Sequences.SelectSeq(tlc2.value.impl.Value,tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to compare string \"a\" with non-string:\n1",
                   SelectSeqMixed)
ASSUME AssertError("Attempted to compare string \"a\" with non-string:\n1",
                   SubsetFcnSetMember)
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.TLC.RandomElement(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to compare string \"a\" with non-string:\n1",
                   RandomElementMixed)
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.TLC.ToString(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to compare string \"a\" with non-string:\n1",
                   ToStringMixed)
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.TLC.Print(tlc2.value.impl.Value,tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to compare string \"a\" with non-string:\n1",
                   PrintMixed)

\* TLC's Java override of TLCEval, which normalizes its argument, doesn't apply
\* to the operator substituted for the constant TLCEval.
ASSUME TLCEvalMixed
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.TLCEval.tlcEval(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel),\nbut it produced the following error:\nAttempted to compare string \"a\" with non-string:\n1",
                   1 \in TLCEval({1, "a"}))

\* ToString and Assert show a record's fields, and the domain of a function
\* that @@ builds, in the order the spec writes them, even though TLC interns
\* fld2 before fld1.
ASSUME ToStringRcd
ASSUME ToStringRcdOrder
ASSUME ToStringFcnOrder
ASSUME AssertError("The first argument of Assert evaluated to FALSE; the second argument was:\n[fld1 |-> 1, fld2 |-> 2]",
                   AssertRcdOrder)
ASSUME AssertError("The first argument of Assert evaluated to FALSE; the second argument was:\n[fld1 |-> 0, fld2 |-> 0]",
                   AssertFcnOrder)
=============================================================================
