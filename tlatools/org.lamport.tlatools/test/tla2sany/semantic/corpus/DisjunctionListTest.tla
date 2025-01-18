----------------------- MODULE DisjunctionListTest --------------------------
EXTENDS Semantics
CONSTANT (* ID: c *) c
VARIABLE (* ID: v *) v

(* ID: ConstantList *)
ConstantList ==
 \/ 1
 \/ 2
 \/ RefersTo(c, "c")
 \/ TRUE

ASSUME RefersTo(ConstantList, "ConstantList")
ASSUME IsLevel(ConstantList, ConstantLevel)

(* ID: VariableList *)
VariableList ==
 \/ RefersTo(v, "v")
 \/ c

THEOREM RefersTo(VariableList, "VariableList")
THEOREM IsLevel(VariableList, VariableLevel)

(* ID: ActionList *)
ActionList ==
 \/ c
 \/ v
 \/ v'

THEOREM RefersTo(ActionList, "ActionList")
THEOREM IsLevel(ActionList, ActionLevel)

(* ID: TemporalList *)
TemporalList ==
 \/ c
 \/ v
 \/ []v

THEOREM RefersTo(TemporalList, "TemporalList")
THEOREM IsLevel(TemporalList, TemporalLevel)

=============================================================================

