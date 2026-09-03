------------------------------ MODULE ValueTest ------------------------------
\* The TLA+ semantics that ValueTest.testIsEmpty expects Value#isEmpty to
\* implement, proved with TLAPS and stated in the order of the test. TLC!Any
\* and the number 1 have no theorem: both are sets, as every TLA+ value is,
\* but TLA+ leaves their elements unspecified, so nothing decides whether
\* either is empty and isEmpty refuses to answer.
\*
\* TLC does not parse this module. Check it from tlatools/org.lamport.tlatools
\* with:
\*   tlapm test/tlc2/value/impl/ValueTest.tla
\*
\* See https://github.com/tlaplus/tlaplus/issues/1407
EXTENDS Integers, Sequences

THEOREM SetEnumNonEmpty == {1} # {} OBVIOUS

THEOREM IntervalEmpty == 1..0 = {} OBVIOUS
THEOREM IntervalNonEmpty == 1..1 # {} OBVIOUS

THEOREM CapEmpty == {1} \cap {2} = {} OBVIOUS
THEOREM CapNonEmpty == {1} \cap {1} # {} OBVIOUS
THEOREM CupEmpty == {} \cup {} = {} OBVIOUS
THEOREM CupNonEmpty == {} \cup {1} # {} OBVIOUS
THEOREM DiffEmpty == {1} \ {1} = {} OBVIOUS
THEOREM DiffNonEmpty == {1} \ {2} # {} OBVIOUS

\* An empty domain yields {<<>>} and not {}.
THEOREM FcnSetEmptyRangeEmpty == [{1} -> {}] = {} OBVIOUS
THEOREM FcnSetEmptyDomainNonEmpty == [{} -> {}] # {} OBVIOUS

THEOREM RcdSetEmptyFieldEmpty == [n1 : {}] = {} OBVIOUS
THEOREM RcdSetNonEmpty == [n1 : {1}] # {} OBVIOUS
THEOREM TupleSetEmptyComponentEmpty == ({} \X {1}) = {} OBVIOUS
THEOREM TupleSetNonEmpty == ({1} \X {1}) # {} OBVIOUS

\* SUBSET S contains {} for every S, hence it is never empty.
THEOREM SubsetOfEmptyNonEmpty == SUBSET {} # {} OBVIOUS
THEOREM SubsetNonEmpty == SUBSET {1} # {} OBVIOUS

THEOREM UnionOfEmptyEmpty == UNION {} = {} OBVIOUS
THEOREM UnionOfEmptyElementEmpty == UNION {{}} = {} OBVIOUS
THEOREM UnionNonEmpty == UNION {{1}} # {} OBVIOUS

THEOREM NatNonEmpty == Nat # {}
  <1>1. 0 \in Nat
    OBVIOUS
  <1>2. QED BY <1>1

THEOREM IntNonEmpty == Int # {}
  <1>1. 0 \in Int
    OBVIOUS
  <1>2. QED BY <1>1

THEOREM StringNonEmpty == STRING # {}
  <1>1. "" \in STRING
    OBVIOUS
  <1>2. QED BY <1>1

THEOREM SeqNonEmpty ==
  ASSUME NEW S
  PROVE  Seq(S) # {}
  <1>1. <<>> \in Seq(S)
    <2>1. <<>> \in [1..0 -> S]
      OBVIOUS
    <2>2. QED BY <2>1
  <1>2. QED BY <1>1
=============================================================================
