----------------------- MODULE AtLegitimateUsesTest -----------------------
\* Legitimate uses of @ that must survive the restrictions on @ as a name.
\* @ is the previous value in EXCEPT, !@ is the positional selector, a
\* label may be named and selected, and "@" may be a string or a field
\* spelled with a keyword.
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

(* ID: Enumeration *)
Enumeration == [f EXCEPT ![1] = {@ \in {1}}]
THEOREM RefersTo(Enumeration, "Enumeration")
THEOREM IsLevel(Enumeration, ConstantLevel)

(* ID: Enumeration2 *)
Enumeration2 ==
    [f EXCEPT ![1] = {@ \in {1}, FALSE}]
THEOREM RefersTo(Enumeration2, "Enumeration2")
THEOREM IsLevel(Enumeration2, ConstantLevel)

(* ID: EnumerationTuple *)
EnumerationTuple == [f EXCEPT ![1] = {<<@>> \in {<<1>>}}]
THEOREM RefersTo(EnumerationTuple, "EnumerationTuple")
THEOREM IsLevel(EnumerationTuple, ConstantLevel)

(* ID: EnumerationMixed *)
EnumerationMixed ==
    [f EXCEPT ![1] = {FALSE, @ \in {1}}]
THEOREM RefersTo(EnumerationMixed, "EnumerationMixed")
THEOREM IsLevel(EnumerationMixed, ConstantLevel)

(* ID: EnumerationTupleMixed *)
EnumerationTupleMixed ==
    [f EXCEPT ![1] = {<<0, @>> \in {<<0, 1>>}}]
THEOREM RefersTo(EnumerationTupleMixed, "EnumerationTupleMixed")
THEOREM IsLevel(EnumerationTupleMixed, ConstantLevel)

(* ID: EnumerationNestedTuple *)
EnumerationNestedTuple ==
    [f EXCEPT ![1] = {<<0, <<@>>>> \in {<<0, <<1>>>>}}]
THEOREM RefersTo(EnumerationNestedTuple, "EnumerationNestedTuple")
THEOREM IsLevel(EnumerationNestedTuple, ConstantLevel)

(* ID: r *)
r == [foo |-> 1]
THEOREM RefersTo(r, "r")
THEOREM IsLevel(r, ConstantLevel)

(* ID: Selection *)
Selection == r.foo
THEOREM RefersTo(Selection, "Selection")
THEOREM IsLevel(Selection, ConstantLevel)

(* ID: Update *)
Update == [r EXCEPT !.foo = @ + 1]
THEOREM RefersTo(Update, "Update")
THEOREM IsLevel(Update, ConstantLevel)

(* ID: KeywordField *)
KeywordField == [THEN |-> 1]
THEOREM RefersTo(KeywordField, "KeywordField")
THEOREM IsLevel(KeywordField, ConstantLevel)

(* ID: KeywordSelection *)
KeywordSelection == KeywordField.THEN
THEOREM RefersTo(KeywordSelection, "KeywordSelection")
THEOREM IsLevel(KeywordSelection, ConstantLevel)

(* ID: KeywordUpdate *)
KeywordUpdate == [KeywordField EXCEPT !.THEN = @]
THEOREM RefersTo(KeywordUpdate, "KeywordUpdate")
THEOREM IsLevel(KeywordUpdate, ConstantLevel)

(* ID: StringKey *)
StringKey == [x \in {"@"} |-> 1]
THEOREM RefersTo(StringKey, "StringKey")
THEOREM IsLevel(StringKey, ConstantLevel)

(* ID: StringSelection *)
StringSelection == StringKey["@"]
THEOREM RefersTo(StringSelection, "StringSelection")
THEOREM IsLevel(StringSelection, ConstantLevel)

(* ID: StringUpdate *)
StringUpdate == [StringKey EXCEPT !["@"] = @]
THEOREM RefersTo(StringUpdate, "StringUpdate")
THEOREM IsLevel(StringUpdate, ConstantLevel)

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

(* ID: Labeled *)
Labeled == \A x \in {1} : lab(x) :: x = 1
THEOREM RefersTo(Labeled, "Labeled")
THEOREM IsLevel(Labeled, ConstantLevel)

(* ID: LabelSelected *)
LabelSelected == Apply(Labeled!lab)
THEOREM RefersTo(LabelSelected, "LabelSelected")
THEOREM IsLevel(LabelSelected, ConstantLevel)

=============================================================================
