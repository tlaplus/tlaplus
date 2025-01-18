------------------------ MODULE ImplicitProofsTest --------------------------
EXTENDS Semantics

CONSTANT (* ID: c *) c
VARIABLE (* ID: v *) v

(* ID: ImmediateImplicitProof *)
LEMMA ImmediateImplicitProof == RefersTo(v, "v")'
<*> RefersTo(c, "c")
(* ID: ImmediateImplicitProof!<0>a *) <0>a RefersTo(v, "v")
<0> QED BY RefersTo(<0>a, "ImmediateImplicitProof!<0>a")

(* ID: ImmediatePlusProof *)
LEMMA ImmediatePlusProof == RefersTo(v, "v")'
<+> RefersTo(c, "c")
(* ID: ImmediatePlusProof!<0>a *) <0>a RefersTo(v, "v")
<0> QED BY RefersTo(<0>a, "ImmediatePlusProof!<0>a")

(* ID: NestedProof *)
COROLLARY NestedProof == []RefersTo(v, "v")
<*> RefersTo(c, "c")
(* ID: NestedProof!<0>a *) <0>a RefersTo(v, "v")
<*> RefersTo(v, "v")'
(* ID: NestedProof!<0>b *) <0>b []RefersTo(v, "v")
  PROOF
  <*> IsLevel(RefersTo(<0>a, "NestedProof!<0>a"), VariableLevel)
  (* ID: NestedProof!<1>a *) <1>a IsLevel(RefersTo(<0>b, "NestedProof!<0>b"), TemporalLevel)
  <*> QED BY RefersTo(<1>a, "NestedProof!<1>a")
<0>d QED BY
  RefersTo(<0>a, "NestedProof!<0>a"),
  RefersTo(<0>b, "NestedProof!<0>b")

=============================================================================

