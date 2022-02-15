---- MODULE AgentRingMC ----
EXTENDS AgentRing, TLC, TLCExt

\* CONSTANT definitions @modelParameterConstants:0N
const_142745588766737000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_142745588768338000 ==
Limits
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_142745588769939000 ==
Prog
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_142745588771440000 ==
TypeInv
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_142745588773041000 ==
Test
----
PostCondition ==
	/\ TLCSet(42, TLCGet("generated"))
	/\ CounterExample =
			[ action |->
			      { << << 1,
			              [ Nodes |-> (0 :> [Load |-> 0] @@ 1 :> [Load |-> 0]),
			                Agent |->
			                    [ Loc |-> 0,
			                      LastLoad |-> 0,
			                      ReadyToMove |-> TRUE,
			                      Task |-> 0 ],
			                CanCreate |-> TRUE ] >>,
			           [ name |-> "CreateTasks",
			             location |->
			                 [ beginLine |-> 82,
			                   beginColumn |-> 3,
			                   endLine |-> 84,
			                   endColumn |-> 35,
			                   module |-> "AgentRing" ] ],
			           << 2,
			              [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 0]),
			                Agent |->
			                    [ Loc |-> 0,
			                      LastLoad |-> 0,
			                      ReadyToMove |-> TRUE,
			                      Task |-> 0 ],
			                CanCreate |-> TRUE ] >> >>,
			        << << 2,
			              [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 0]),
			                Agent |->
			                    [ Loc |-> 0,
			                      LastLoad |-> 0,
			                      ReadyToMove |-> TRUE,
			                      Task |-> 0 ],
			                CanCreate |-> TRUE ] >>,
			           [ name |-> "Move",
			             location |->
			                 [ beginLine |-> 58,
			                   beginColumn |-> 3,
			                   endLine |-> 60,
			                   endColumn |-> 35,
			                   module |-> "AgentRing" ] ],
			           << 3,
			              [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 0]),
			                Agent |->
			                    [ Loc |-> 1,
			                      LastLoad |-> 0,
			                      ReadyToMove |-> FALSE,
			                      Task |-> 0 ],
			                CanCreate |-> TRUE ] >> >>,
			        << << 3,
			              [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 0]),
			                Agent |->
			                    [ Loc |-> 1,
			                      LastLoad |-> 0,
			                      ReadyToMove |-> FALSE,
			                      Task |-> 0 ],
			                CanCreate |-> TRUE ] >>,
			           [ name |-> "CreateTasks",
			             location |->
			                 [ beginLine |-> 82,
			                   beginColumn |-> 3,
			                   endLine |-> 84,
			                   endColumn |-> 35,
			                   module |-> "AgentRing" ] ],
			           << 4,
			              [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 2]),
			                Agent |->
			                    [ Loc |-> 1,
			                      LastLoad |-> 0,
			                      ReadyToMove |-> FALSE,
			                      Task |-> 0 ],
			                CanCreate |-> TRUE ] >> >>,
			        << << 4,
			              [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 2]),
			                Agent |->
			                    [ Loc |-> 1,
			                      LastLoad |-> 0,
			                      ReadyToMove |-> FALSE,
			                      Task |-> 0 ],
			                CanCreate |-> TRUE ] >>,
			           [ name |-> "Stop",
			             location |->
			                 [ beginLine |-> 78,
			                   beginColumn |-> 3,
			                   endLine |-> 79,
			                   endColumn |-> 31,
			                   module |-> "AgentRing" ] ],
			           << 5,
			              [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 2]),
			                Agent |->
			                    [ Loc |-> 1,
			                      LastLoad |-> 0,
			                      ReadyToMove |-> FALSE,
			                      Task |-> 0 ],
			                CanCreate |-> FALSE ] >> >>,
			        << << 5,
			              [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 2]),
			                Agent |->
			                    [ Loc |-> 1,
			                      LastLoad |-> 0,
			                      ReadyToMove |-> FALSE,
			                      Task |-> 0 ],
			                CanCreate |-> FALSE ] >>,
			           [ name |-> "LookAndAct",
			             location |->
			                 [ beginLine |-> 63,
			                   beginColumn |-> 3,
			                   endLine |-> 75,
			                   endColumn |-> 24,
			                   module |-> "AgentRing" ] ],
			           << 6,
			              [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 1]),
			                Agent |->
			                    [ Loc |-> 1,
			                      LastLoad |-> 1,
			                      ReadyToMove |-> TRUE,
			                      Task |-> 1 ],
			                CanCreate |-> FALSE ] >> >> },
			  state |->
			      { << 1,
			           [ Nodes |-> (0 :> [Load |-> 0] @@ 1 :> [Load |-> 0]),
			             Agent |->
			                 [Loc |-> 0, LastLoad |-> 0, ReadyToMove |-> TRUE, Task |-> 0],
			             CanCreate |-> TRUE ] >>,
			        << 2,
			           [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 0]),
			             Agent |->
			                 [Loc |-> 0, LastLoad |-> 0, ReadyToMove |-> TRUE, Task |-> 0],
			             CanCreate |-> TRUE ] >>,
			        << 3,
			           [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 0]),
			             Agent |->
			                 [Loc |-> 1, LastLoad |-> 0, ReadyToMove |-> FALSE, Task |-> 0],
			             CanCreate |-> TRUE ] >>,
			        << 4,
			           [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 2]),
			             Agent |->
			                 [Loc |-> 1, LastLoad |-> 0, ReadyToMove |-> FALSE, Task |-> 0],
			             CanCreate |-> TRUE ] >>,
			        << 5,
			           [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 2]),
			             Agent |->
			                 [Loc |-> 1, LastLoad |-> 0, ReadyToMove |-> FALSE, Task |-> 0],
			             CanCreate |-> FALSE ] >>,
			        << 6,
			           [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 1]),
			             Agent |->
			                 [Loc |-> 1, LastLoad |-> 1, ReadyToMove |-> TRUE, Task |-> 1],
			             CanCreate |-> FALSE ] >> } ]
	/\ ToTrace(CounterExample) =
				<< [ Nodes |-> (0 :> [Load |-> 0] @@ 1 :> [Load |-> 0]),
			     Agent |-> [Loc |-> 0, LastLoad |-> 0, ReadyToMove |-> TRUE, Task |-> 0],
			     CanCreate |-> TRUE ],
			   [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 0]),
			     Agent |-> [Loc |-> 0, LastLoad |-> 0, ReadyToMove |-> TRUE, Task |-> 0],
			     CanCreate |-> TRUE ],
			   [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 0]),
			     Agent |-> [Loc |-> 1, LastLoad |-> 0, ReadyToMove |-> FALSE, Task |-> 0],
			     CanCreate |-> TRUE ],
			   [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 2]),
			     Agent |-> [Loc |-> 1, LastLoad |-> 0, ReadyToMove |-> FALSE, Task |-> 0],
			     CanCreate |-> TRUE ],
			   [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 2]),
			     Agent |-> [Loc |-> 1, LastLoad |-> 0, ReadyToMove |-> FALSE, Task |-> 0],
			     CanCreate |-> FALSE ],
			   [ Nodes |-> (0 :> [Load |-> 2] @@ 1 :> [Load |-> 1]),
			     Agent |-> [Loc |-> 1, LastLoad |-> 1, ReadyToMove |-> TRUE, Task |-> 1],
			     CanCreate |-> FALSE ] >>

	
=============================================================================
\* Modification History
\* Created Fri Mar 27 12:31:27 CET 2015 by makuppe
