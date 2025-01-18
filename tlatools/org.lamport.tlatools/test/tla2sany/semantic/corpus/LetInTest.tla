---------------------------- MODULE LetInTest -------------------------------
EXTENDS Semantics

CONSTANT (* ID: c *) c
VARIABLE (* ID: v *) v

BasicLetIn ==
  LET
    (* ID: BasicLetIn!def *) def == c
  IN
    /\ RefersTo(def, "BasicLetIn!def")
    /\ IsLevel(def, ConstantLevel)
THEOREM IsLevel(BasicLetIn, ConstantLevel)

LetInWithSameDefName ==
  LET
    (* ID: LetInWithSameDefName!def *) def == v
  IN
    /\ RefersTo(def, "LetInWithSameDefName!def")
    /\ IsLevel(def, VariableLevel)
THEOREM IsLevel(LetInWithSameDefName, VariableLevel)

LetInWithMultipleDefs ==
  LET
    (* ID: LetInWithMultipleDefs!def1 *) def1(x) == c = x
    (* ID: LetInWithMultipleDefs!def2 *) def2 == RefersTo(def1(v), "LetInWithMultipleDefs!def1")
  IN
    /\ RefersTo(def1(c), "LetInWithMultipleDefs!def1")
    /\ IsLevel(def1(c), ConstantLevel)
    /\ RefersTo(def2, "LetInWithMultipleDefs!def2")
    /\ IsLevel(def2, VariableLevel)
THEOREM IsLevel(LetInWithMultipleDefs, VariableLevel)

LetInWithSymbols ==
  LET
    (* ID: LetInWithSymbols!+ *) x + y == v'
    (* ID: LetInWithSymbols!^* *) x^* == RefersTo(v + c, "LetInWithSymbols!+")
  IN
    /\ RefersTo(1 + 2, "LetInWithSymbols!+")
    /\ IsLevel(1 + 2, ActionLevel)
    /\ RefersTo(1^*, "LetInWithSymbols!^*")
    /\ IsLevel(1^*, ActionLevel)
THEOREM IsLevel(LetInWithSymbols, ActionLevel)

RecursiveLetIn ==
  LET
    RECURSIVE op(_), _*_, _^#
    (* ID: RecursiveLetIn!op *) op(x) == RefersTo(op(x), "RecursiveLetIn!op")
    (* ID: RecursiveLetIn!* *) x * y == RefersTo(x * y, "RecursiveLetIn!*")
    (* ID: RecursiveLetIn!^# *) x^# == RefersTo(x^#, "RecursiveLetIn!^#")
  IN
    /\ RefersTo(op(1), "RecursiveLetIn!op")
    /\ IsLevel(op(1), ConstantLevel)
    /\ RefersTo(1 * 2, "RecursiveLetIn!*")
    /\ IsLevel(1 * 2, ConstantLevel)
    /\ RefersTo(1^#, "RecursiveLetIn!^#")
    /\ IsLevel(1^#, ConstantLevel)
THEOREM IsLevel(RecursiveLetIn, ConstantLevel)

=============================================================================
