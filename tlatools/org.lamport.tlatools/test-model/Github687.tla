---------------------------- MODULE Github687 ----------------------------
CONSTANTS Commands, Slots
VARIABLES log

Init == 
	log = [s \in Slots |-> {}]

Next ==
	\E s \in Slots:
		/\ log[s] = {}
	    /\ \E v \in Commands:
	    	log' = [log EXCEPT ![s] = {v}]

Spec == 
	Init /\ [][Next]_<<log>> /\ WF_log(Next)

ConsensusOnSlot(s) == 
	INSTANCE Consensus 
	WITH Values <- Commands, 
	     chosen_values <- log[s], 
	     SomeConstant <- {"a", "b"}

Correct ==
	\A s \in Slots: ConsensusOnSlot(s)!Spec

===========================================================================

---------------------------- MODULE Consensus ----------------------------
CONSTANT Values, SomeConstant
VARIABLE chosen_values

Init == chosen_values = {}
Next == chosen_values = {} /\ \E v \in Values: chosen_values' = {v}
Spec == 
	/\ Init /\ [][Next]_<<chosen_values>>
	\* The fairness constraint is here to trigger a code path in SpecProcessor.
	\* With regards to the spec, quantifying over SC is meaningless.
	/\ \A s \in SomeConstant: WF_<<chosen_values>>(Next)
===========================================================================

---------------------------- CONFIG Github687 ----------------------------
SPECIFICATION Spec
CONSTANT Commands = {Read, Write}
CONSTANT Slots = {Slot1, Slot2}
PROPERTY Correct
CHECK_DEADLOCK FALSE
===========================================================================
