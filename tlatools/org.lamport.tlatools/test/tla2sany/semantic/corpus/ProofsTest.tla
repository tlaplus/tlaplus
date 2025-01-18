---------------------------- MODULE ProofsTest ------------------------------
EXTENDS Semantics

CONSTANT (* ID: c *) c
VARIABLE (* ID: v *) v

(* ID: ObviousProof *)
THEOREM ObviousProof == RefersTo(c, "c")
PROOF OBVIOUS

(* ID: OmittedProof *)
PROPOSITION OmittedProof == RefersTo(v, "v")
PROOF OMITTED

(* ID: ProofByDef *)
LEMMA ProofByDef == RefersTo(v, "v")'
PROOF BY RefersTo(ObviousProof, "ObviousProof") DEF OmittedProof

(* ID: ProofByMultipleDefs *)
COROLLARY ProofByMultipleDefs == []RefersTo(v, "v")
PROOF BY
  ONLY
    RefersTo(ObviousProof, "ObviousProof"),
    RefersTo(OmittedProof, "OmittedProof")
  DEFS
    OmittedProof,
    ProofByDef

(* ID: ProofByQED *)
THEOREM ProofByQED == RefersTo(c, "c")
PROOF
  (* ID: ProofByQED!<1>a *)
  <1>a QED

(* ID: ProofByQED *)
PROPOSITION ProofByQED == RefersTo(v, "v")
PROOF
  (* ID: ProofByQED!<1>a *)
  <1>a QED BY RefersTo(ObviousProof, "ObviousProof")

(* ID: MultiStepProof *)
LEMMA MultiStepProof == RefersTo(v, "v")'
PROOF
  (* ID: ProofByQED!<1>a *)
  <1>a RefersTo(c, "c")
  <1>b RefersTo(<1>a, "ProofByQED!<1>a")
  <1>c QED BY <1>b

(* ID: NestedProof *)
COROLLARY NestedProof == []RefersTo(v, "v")
(* ID: NestedProof!<1>a *) <1>a RefersTo(c, "c")
(* ID: NestedProof!<1>b *) <1>b RefersTo(v, "v")
(* ID: NestedProof!<1>c *) <1>c RefersTo(v, "v")'
(* ID: NestedProof!<1>d *) <1>d []RefersTo(v, "v")
  (* ID: NestedProof!<2>a *) <2>a IsLevel(RefersTo(<1>a, "NestedProof!<1>a"), ConstantLevel)
  (* ID: NestedProof!<2>b *) <2>b IsLevel(RefersTo(<1>b, "NestedProof!<1>b"), VariableLevel)
  (* ID: NestedProof!<2>c *) <2>c IsLevel(RefersTo(<1>c, "NestedProof!<1>c"), ActionLevel)
  (* ID: NestedProof!<2>d *) <2>d IsLevel(RefersTo(<1>d, "NestedProof!<1>d"), TemporalLevel)
  <2>d QED
    (* ID: NestedProof!<3>a *) <3>a IsLevel(RefersTo(<2>a, "NestedProof!<2>a"), ConstantLevel)
    (* ID: NestedProof!<3>b *) <3>b IsLevel(RefersTo(<2>b, "NestedProof!<2>b"), VariableLevel)
    (* ID: NestedProof!<3>c *) <3>c IsLevel(RefersTo(<2>c, "NestedProof!<2>c"), ActionLevel)
    (* ID: NestedProof!<3>d *) <3>d IsLevel(RefersTo(<2>d, "NestedProof!<2>d"), TemporalLevel)
    <3> QED BY
      RefersTo(<3>a, "NestedProof!<3>a"),
      RefersTo(<3>b, "NestedProof!<3>b"),
      RefersTo(<3>c, "NestedProof!<3>c"),
      RefersTo(<3>d, "NestedProof!<3>d")
<1>d QED BY
  RefersTo(<1>a, "NestedProof!<1>a"),
  RefersTo(<1>b, "NestedProof!<1>b"),
  RefersTo(<1>c, "NestedProof!<1>c"),
  RefersTo(<1>d, "NestedProof!<1>d")

(* ID: DefineStepProof *)
THEOREM DefineStepProof == TRUE
<1> DEFINE (* ID: DefineStepProof!f *)
  f((* ID: DefineStepProof!f!x *) x) ==
    RefersTo(x, "DefineStepProof!f!x")
<1> DEFINE (* ID: DefineStepProof!< *) x < y == RefersTo(v, "v")
<1> DEFINE (* ID: DefineStepProof!^* *) x^* == RefersTo(v, "v")'
<1> DEFINE (* ID: DefineStepProof!g *) g[x \in {}] == []x
<1> DEFINE h == INSTANCE Semantics
<1> QED BY
  IsLevel(RefersTo(f(c), "DefineStepProof!f"), ConstantLevel),
  IsLevel(RefersTo(c < c, "DefineStepProof!<"), VariableLevel),
  IsLevel(RefersTo(c^*, "DefineStepProof!^*"), ActionLevel),
  IsLevel(RefersTo(g, "DefineStepProof!g"), TemporalLevel),
  RefersTo(h!RefersTo(DefineStepProof, "DefineStepProof"), "Semantics!RefersTo")

THEOREM RedefineStepProof == TRUE
<1> DEFINE (* ID: RedefineStepProof!f *) f(x) == x
<1> QED BY RefersTo(f(c), "RedefineStepProof!f")

(* ID: TakeStepProof *)
THEOREM TakeStepProof == TRUE
<1>a TAKE
  (* ID: TakeStepProof!x *) x, (* ID: TakeStepProof!y *) y
<1>b TAKE
  <<(* ID: TakeStepProof!z *) z, (* ID: TakeStepProof!w *) w>> \in RefersTo(v, "v"),
  (* ID: TakeStepProof!u *) u \in RefersTo(v, "v")
<1> QED BY
  IsLevel(RefersTo(x, "TakeStepProof!x"), ConstantLevel),
  IsLevel(RefersTo(y, "TakeStepProof!y"), ConstantLevel),
  IsLevel(RefersTo(z, "TakeStepProof!z"), ConstantLevel),
  IsLevel(RefersTo(w, "TakeStepProof!w"), ConstantLevel),
  IsLevel(RefersTo(u, "TakeStepProof!u"), ConstantLevel)

(* ID: PickStepProof *)
THEOREM PickStepProof == TRUE
<1>a PICK
  (* ID: PickStepProof!x *) x, (* ID: PickStepProof!y *) y :
    RefersTo(v, "v")
<1>b PICK
  <<(* ID: PickStepProof!z *) z, (* ID: PickStepProof!w *) w>> \in RefersTo(v, "v"),
  (* ID: PickStepProof!u *) u \in RefersTo(v, "v") :
    RefersTo(v, "v")'
<1> QED BY
  IsLevel(RefersTo(x, "PickStepProof!x"), ConstantLevel),
  IsLevel(RefersTo(y, "PickStepProof!y"), ConstantLevel),
  IsLevel(RefersTo(z, "PickStepProof!z"), ConstantLevel),
  IsLevel(RefersTo(w, "PickStepProof!w"), ConstantLevel),
  IsLevel(RefersTo(u, "PickStepProof!u"), ConstantLevel)

(* ID: UseStepProof *)
THEOREM UseStepProof == TRUE
<1>a USE
  RefersTo(PickStepProof, "PickStepProof"),
  RefersTo(TakeStepProof, "TakeStepProof"),
  RefersTo(DefineStepProof, "DefineStepProof")
<1> QED

=============================================================================

