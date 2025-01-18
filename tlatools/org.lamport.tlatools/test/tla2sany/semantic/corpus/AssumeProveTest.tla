-------------------------- MODULE AssumeProveTest ---------------------------
EXTENDS Semantics
CONSTANT (* ID: c *) c
VARIABLE (* ID: v *) v

\* Basic ASSUME/PROVE test
\* Cannot use RefersTo to test that ap refers to "ap" since SANY types ap as
\* an ASSUME/PROVE and requires operator parameters to be expressions.
\* Inferring that ap is correctly resolved due to lack of error here is best
\* we can do.

(* ID: ap *)
THEOREM ap ==
  ASSUME RefersTo(c, "c"), RefersTo(v, "v")
  PROVE IsLevel(c = v, VariableLevel)
PROOF BY ap

\* Test ASSUME/PROVE introducing new identifiers

(* ID: ap2 *)
THEOREM ap2 ==
  ASSUME
    NEW CONSTANT (* ID: ap2!c2 *) c2,
    RefersTo(c2, "ap2!c2"),
    IsLevel(c2, ConstantLevel),
    NEW (* ID: ap2!c3 *) c3,
    RefersTo(c3, "ap2!c3"),
    IsLevel(c3, ConstantLevel),
    VARIABLE (* ID: ap2!v2 *) v2,
    RefersTo(v2, "ap2!v2"),
    IsLevel(v2, VariableLevel),
    NEW STATE (* ID: ap2!s *) s,
    RefersTo(s, "ap2!s"),
    IsLevel(s, VariableLevel),
    ACTION (* ID: ap2!a *) a,
    RefersTo(a, "ap2!a"),
    IsLevel(a, ActionLevel),
    NEW TEMPORAL (* ID: ap2!t *) t,
    RefersTo(t, "ap2!t"),
    IsLevel(t, TemporalLevel)
  PROVE
    /\ RefersTo(c2, "ap2!c2")
    /\ IsLevel(c2, ConstantLevel)
    /\ RefersTo(c3, "ap2!c3")
    /\ IsLevel(c3, ConstantLevel)
    /\ RefersTo(v2, "ap2!v2")
    /\ IsLevel(v2, VariableLevel)
    /\ RefersTo(s, "ap2!s")
    /\ IsLevel(s, VariableLevel)
    /\ RefersTo(a, "ap2!a")
    /\ IsLevel(a, ActionLevel)
    (* Cannot have temporal-level and action-level formulas in same expression *)
PROOF BY
  RefersTo(c2, "ap2!c2"),
  IsLevel(c2, ConstantLevel),
  RefersTo(c3, "ap2!c3"),
  IsLevel(c3, ConstantLevel),
  RefersTo(v2, "ap2!v2"),
  IsLevel(v2, VariableLevel),
  RefersTo(s, "ap2!s"),
  IsLevel(s, VariableLevel),
  RefersTo(a, "ap2!a"),
  IsLevel(a, ActionLevel),
  RefersTo(t, "ap2!t"),
  IsLevel(t, TemporalLevel),
  ap2

\* Test ASSUME/PROVE can reintroduce same identifiers without error

(* ID: ap3 *)
THEOREM ap3 ==
  ASSUME
    CONSTANT (* ID: ap3!c2 *) c2 \in {},
    RefersTo(c2, "ap3!c2"),
    IsLevel(c2, ConstantLevel),
    NEW (* ID: ap3!c3 *) c3 \in {1,2,3,4,5},
    RefersTo(c3, "ap3!c3"),
    IsLevel(c3, ConstantLevel),
    NEW VARIABLE (* ID: ap3!v2 *) v2,
    RefersTo(v2, "ap3!v2"),
    IsLevel(v2, VariableLevel),
    STATE (* ID: ap3!s *) s,
    RefersTo(s, "ap3!s"),
    IsLevel(s, VariableLevel),
    NEW ACTION (* ID: ap3!a *) a,
    RefersTo(a, "ap3!a"),
    IsLevel(a, ActionLevel),
    TEMPORAL (* ID: ap3!t *) t,
    RefersTo(t, "ap3!t"),
    IsLevel(t, TemporalLevel)
  PROVE
    /\ RefersTo(c2, "ap3!c2")
    /\ IsLevel(c2, ConstantLevel)
    /\ RefersTo(c3, "ap3!c3")
    /\ IsLevel(c3, ConstantLevel)
    /\ RefersTo(v2, "ap3!v2")
    /\ IsLevel(v2, VariableLevel)
    /\ RefersTo(s, "ap3!s")
    /\ IsLevel(s, VariableLevel)
    /\ RefersTo(a, "ap3!a")
    /\ IsLevel(a, ActionLevel)
    (* Cannot have temporal-level and action-level formulas in same expression *)
PROOF BY
  RefersTo(c2, "ap3!c2"),
  IsLevel(c2, ConstantLevel),
  RefersTo(c3, "ap3!c3"),
  IsLevel(c3, ConstantLevel),
  RefersTo(v2, "ap3!v2"),
  IsLevel(v2, VariableLevel),
  RefersTo(s, "ap3!s"),
  IsLevel(s, VariableLevel),
  RefersTo(a, "ap3!a"),
  IsLevel(a, ActionLevel),
  RefersTo(t, "ap3!t"),
  IsLevel(t, TemporalLevel),
  ap3

\* Test nested ASSUME/PROVE with labels

(* ID: ap4 *)
THEOREM ap4 ==
  ASSUME
    innerAP1 ::
      ASSUME NEW (* ID: ap4!c2 *) c2 \in {1,2,3}
      PROVE RefersTo(c2, "ap4!c2"),
    innerAP2 ::
      ASSUME TRUE
      PROVE TRUE,
    exprLbl :: TRUE
  PROVE TRUE
PROOF BY ap4, ap4!innerAP1, ap4!innerAP2, ap4!exprLbl

\* Test introducing new operators in ASSUME/PROVE blocks
\* New operators can be introduced with every keyword except VARIABLE

(* ID: ap5 *)
THEOREM ap5 ==
  ASSUME
    NEW (* ID: ap5!f *) f(_, _),
    RefersTo(f(1, 2), "ap5!f"),
    IsLevel(f(1, 2), ConstantLevel),
    NEW STATE (* ID: ap5!+ *) _+_,
    RefersTo(1 + 2, "ap5!+"),
    IsLevel(1 + 2, VariableLevel),
    ACTION (* ID: ap5!- *) -._,
    \* https://github.com/tlaplus/tlaplus/issues/1130
    (* RefersTo(-1, "ap5!-"), *)
    IsLevel(-1, ActionLevel),
    NEW TEMPORAL (* ID: ap5!^+ *) _^+,
    RefersTo(1^+, "ap5!^+"),
    IsLevel(1^+, TemporalLevel)
  PROVE TRUE
PROOF BY ap5

=============================================================================
