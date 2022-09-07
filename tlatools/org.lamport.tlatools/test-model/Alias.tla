






---- MODULE Alias ----
EXTENDS Integers, TLC, Sequences, TLCExt

VARIABLES x, y
vars == <<x,y>>

A ==
/\ y' = ~y
/\ x < 4
/\ x' = x + 1

B ==
/\ y' = ~y
/\ x = 4
/\ x' = 1             

Next == A \/ B

Spec == x = 1 /\ y = FALSE /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

Inv == x < 4

Prop == <>(x > 4)

Animation(e1,e2) == "e1: " \o ToString(e1) \o " e2: " \o ToString(e2)

\* An expression that is evaluated on the pair of states
\* s and t and printed in place of s in an error trace.
\* Useful to:
\* - filter out variables (not shown below)
\* - rename variables
\* - map variables (e.g. animation)
\* - additional trace expressions
\* TLC ignores the original state if the evaluation of
\* Alias fails.
Alias == IF TLCGet("config").mode = "simulate" THEN
         [y |-> y, \* x and y reordered.
          x |-> x, 
          a |-> x' - x, 
          b |-> x' = x,
          anim |-> Animation(x, y), \* Animation
          te |-> ENABLED Next,      \* Trace Expression
          TLCGetAction |-> TLCGet("action"),
          lvl |-> [ i \in {1,2} |-> TLCGet("level")]]
         ELSE 
         [y |-> y, \* x and y reordered.
          x |-> x, 
          a |-> x' - x, 
          b |-> x' = x,
          anim |-> Animation(x, y), \* Animation
          te |-> ENABLED Next,      \* Trace Expression
          lvl |-> [ i \in {1,2} |-> TLCGet("level")],
          trc |-> Trace]
         

PostCondition ==
	/\ TLCSet(42, TLCGet("generated"))
  	/\ CounterExample = 
			[ action |->
			      { << <<1, [x |-> 1, y |-> FALSE]>>,
			           [ name |-> "A",
			             location |->
			                 [ beginLine |-> 15,
			                   beginColumn |-> 1,
			                   endLine |-> 17,
			                   endColumn |-> 13,
			                   module |-> "Alias" ] ],
			           <<2, [x |-> 2, y |-> TRUE]>> >>,
			        << <<2, [x |-> 2, y |-> TRUE]>>,
			           [ name |-> "A",
			             location |->
			                 [ beginLine |-> 15,
			                   beginColumn |-> 1,
			                   endLine |-> 17,
			                   endColumn |-> 13,
			                   module |-> "Alias" ] ],
			           <<3, [x |-> 3, y |-> FALSE]>> >>,
			        << <<3, [x |-> 3, y |-> FALSE]>>,
			           [ name |-> "A",
			             location |->
			                 [ beginLine |-> 15,
			                   beginColumn |-> 1,
			                   endLine |-> 17,
			                   endColumn |-> 13,
			                   module |-> "Alias" ] ],
			           <<4, [x |-> 4, y |-> TRUE]>> >> },
			  state |->
			      { <<1, [x |-> 1, y |-> FALSE]>>,
			        <<2, [x |-> 2, y |-> TRUE]>>,
			        <<3, [x |-> 3, y |-> FALSE]>>,
			        <<4, [x |-> 4, y |-> TRUE]>> } ]
=======================

---- CONFIG Alias ----
SPECIFICATION FairSpec
INVARIANT Inv
PROPERTY Prop
ALIAS Alias
POSTCONDITION PostCondition
======================


\* FairSpec => []Inv
Error: Invariant Inv is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ y = FALSE
/\ x = 1
/\ a = 1
/\ b = FALSE

State 2: <Action line 11, col 34 to line 11, col 46 of module Alias>
/\ y = TRUE
/\ x = 2
/\ a = 1
/\ b = FALSE

State 3: <Action line 11, col 34 to line 11, col 46 of module Alias>
/\ y = FALSE
/\ x = 3
/\ a = 1
/\ b = FALSE

State 4: <Action line 11, col 34 to line 11, col 46 of module Alias>
/\ y = TRUE
/\ x = 4
/\ a = 0     \* Stuttering
/\ b = TRUE  \* Stuttering

-------------------------------
\* Spec => Prop
Error: Temporal properties were violated.
Error: The following behavior constitutes a counter-example:

State 1: <Initial predicate>
/\ y = FALSE
/\ x = 1
/\ a = 0     \* Stuttering
/\ b = TRUE  \* Stuttering

State 2: Stuttering

-------------------------------
\* FairSpec => Prop
Error: Temporal properties were violated.
Error: The following behavior constitutes a counter-example:

State 1: <Initial predicate>
/\ y = FALSE
/\ x = 1
/\ a = 1
/\ b = FALSE

State 2: <Next line 17, col 9 to line 21, col 23 of module Alias>
/\ y = TRUE
/\ x = 2
/\ a = 1
/\ b = FALSE

State 3: <Next line 17, col 9 to line 21, col 23 of module Alias>
/\ y = FALSE
/\ x = 3
/\ a = 1
/\ b = FALSE

State 4: <Next line 17, col 9 to line 21, col 23 of module Alias>
/\ y = TRUE
/\ x = 4
/\ a = -3      \* State 1 is successor
/\ b = FALSE   \* State 1 is successor

Back to state 1: <Next line 17, col 9 to line 21, col 23 of module Alias>

-------------------------------

