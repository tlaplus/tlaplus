----------------------- MODULE AtLegitimateUsesTest -----------------------
\* @ is the previous value in EXCEPT, and !@ is the positional selector.
EXTENDS Semantics, Naturals

(* ID: f *)
f == <<1>>
THEOREM RefersTo(f, "f")
THEOREM IsLevel(f, ConstantLevel)

(* ID: Simple *)
Simple == [f EXCEPT ![1] = @]
THEOREM RefersTo(Simple, "Simple")
THEOREM IsLevel(Simple, ConstantLevel)

(* ID: Arithmetic *)
Arithmetic == [f EXCEPT ![1] = @ + 1]
THEOREM RefersTo(Arithmetic, "Arithmetic")
THEOREM IsLevel(Arithmetic, ConstantLevel)

(* ID: Apply *)
Apply(P(_)) == P(1)

(* ID: Quantified *)
Quantified == \A x \in {1} : x = 1
THEOREM RefersTo(Quantified, "Quantified")
THEOREM IsLevel(Quantified, ConstantLevel)

(* ID: Selected *)
Selected == Apply(Quantified!@)
THEOREM RefersTo(Selected, "Selected")
THEOREM IsLevel(Selected, ConstantLevel)

=============================================================================
