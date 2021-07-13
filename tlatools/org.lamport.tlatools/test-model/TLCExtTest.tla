------------- CONFIG TLCExtTest ---------
SPECIFICATION Spec
INVARIANT Inv
===================

---- MODULE TLCExtTest ----

EXTENDS TLCExt, TLC, FiniteSets, Sequences, Naturals

VARIABLE mvs

Init ==
  mvs = { TLCModelValue("T_MV" \o ToString(i)) : i \in 1..3 }

Spec == 
  Init /\ [][UNCHANGED mvs]_mvs

Inv ==
  /\ Cardinality(mvs) = 3
  /\ TLCModelValue("T_MV1") \in mvs
  /\ TLCModelValue("T_MV2") \in mvs
  /\ TLCModelValue("T_MV3") \in mvs

-------------------------------------------------

ASSUME ToString(TLCModelValue("T_MyMV")) = "T_MyMV"
ASSUME ToString(TLCModelValue("T_MyMV")) # ""

ASSUME TLCModelValue("T_MyMV") = TLCModelValue("T_MyMV")
ASSUME TLCModelValue("T_MyMV") # TLCModelValue("T_YourMV")
ASSUME AssertError(
  "Attempted to check equality of the differently-typed model values T_MyMV and S_MyMV",
  TLCModelValue("T_MyMV") = TLCModelValue("S_MyMV"))
==================================
