---------------------- MODULE Github1521SemanticsProof ----------------------
EXTENDS Github1521Semantics, Naturals, TLAPS

LEMMA VariantA_DirectPrime ==
  ASSUME x \in BOOLEAN, x' \in BOOLEAN
  PROVE  DirectPrime <=> Step(TRUE)
  BY Isa DEF DirectPrime, Step

LEMMA VariantB_IndirectPrime ==
  ASSUME x \in BOOLEAN, x' \in BOOLEAN
  PROVE  IndirectPrime <=> Step(TRUE)
  BY Isa DEF IndirectPrime, Step

LEMMA VariantC_Unchanged ==
  ASSUME x \in BOOLEAN, x' \in BOOLEAN
  PROVE  Unchanged <=> Step(TRUE)
  BY Isa DEF Unchanged, Step

LEMMA VariantD_PrimedPath ==
  ASSUME x \in BOOLEAN, x' \in BOOLEAN
  PROVE  PrimedPath <=> Step(TRUE)
  BY Isa DEF PrimedPath, Step, Index

LEMMA VariantE_PriorUpdate ==
  ASSUME x \in BOOLEAN, x' \in BOOLEAN
  PROVE  PriorUpdate <=> Step(TRUE)
  BY Isa DEF PriorUpdate, Step

LEMMA VariantF_NestedBase ==
  ASSUME x \in BOOLEAN, x' \in BOOLEAN
  PROVE  NestedBase <=> Step(TRUE)
  BY Isa DEF NestedBase, Step

LEMMA VariantG_NestedPath ==
  ASSUME x \in BOOLEAN, x' \in BOOLEAN
  PROVE  NestedPath <=> Step(TRUE)
  BY Isa DEF NestedPath, Step

LEMMA VariantH_NestedSelector ==
  ASSUME x \in BOOLEAN, x' \in BOOLEAN
  PROVE  NestedSelector <=> Step(TRUE)
  BY Isa DEF NestedSelector, Step

LEMMA VariantI_OperatorArgument ==
  ASSUME x \in BOOLEAN, x' \in BOOLEAN
  PROVE  OperatorArgument <=> Step(TRUE)
  BY Isa DEF OperatorArgument, Step, WithArg

LEMMA VariantJ_WholePrime ==
  ASSUME x \in BOOLEAN, x' \in BOOLEAN
  PROVE  WholePrime <=> Step(TRUE)
  BY Isa DEF WholePrime, Step

LEMMA VariantK_Unprimed ==
  ASSUME x \in BOOLEAN, x' \in BOOLEAN
  PROVE  Unprimed <=> Step(TRUE)
  BY Isa DEF Unprimed, Step

LEMMA VariantL_Enabled ==
  ASSUME x \in BOOLEAN, x' \in BOOLEAN
  PROVE  Enabled <=> Step(TRUE)
  BY ExpandENABLED, Isa DEF Enabled, Step

=============================================================================
