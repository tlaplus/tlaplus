---- MODULE MCa ----
EXTENDS CodeplexBug8, TLC, TLCExt

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_14273156623644000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_14273156623745000 ==
x=1 ~> x=0
----
PostCondition ==
	/\ TLCSet(42, TLCGet("generated"))
	/\ \/ CounterExample = [state |-> {}, action |-> {}]
	   \/ /\ CounterExample = 
				[ state |->
				      { <<1, [x |-> 1, b |-> FALSE]>>,
				        <<2, [x |-> 2, b |-> TRUE]>>,
				        <<3, [x |-> 2, b |-> FALSE]>>,
				        <<4, [x |-> 3, b |-> TRUE]>>,
				        <<5, [x |-> 3, b |-> FALSE]>>,
				        <<6, [x |-> 4, b |-> TRUE]>>,
				        <<7, [x |-> 4, b |-> FALSE]>>,
				        <<8, [x |-> 5, b |-> TRUE]>> },
				  action |->
				      { << <<1, [x |-> 1, b |-> FALSE]>>,
				           [ name |-> "B",
				             location |->
				                 [ beginLine |-> 11,
				                   beginColumn |-> 6,
				                   endLine |-> 13,
				                   endColumn |-> 18,
				                   module |-> "CodeplexBug8" ] ],
				           <<2, [x |-> 2, b |-> TRUE]>> >>,
				        << <<2, [x |-> 2, b |-> TRUE]>>,
				           [ name |-> "A",
				             location |->
				                 [ beginLine |-> 6,
				                   beginColumn |-> 6,
				                   endLine |-> 9,
				                   endColumn |-> 19,
				                   module |-> "CodeplexBug8" ] ],
				           <<3, [x |-> 2, b |-> FALSE]>> >>,
				        << <<3, [x |-> 2, b |-> FALSE]>>,
				           [ name |-> "B",
				             location |->
				                 [ beginLine |-> 11,
				                   beginColumn |-> 6,
				                   endLine |-> 13,
				                   endColumn |-> 18,
				                   module |-> "CodeplexBug8" ] ],
				           <<4, [x |-> 3, b |-> TRUE]>> >>,
				        << <<4, [x |-> 3, b |-> TRUE]>>,
				           [ name |-> "A",
				             location |->
				                 [ beginLine |-> 6,
				                   beginColumn |-> 6,
				                   endLine |-> 9,
				                   endColumn |-> 19,
				                   module |-> "CodeplexBug8" ] ],
				           <<5, [x |-> 3, b |-> FALSE]>> >>,
				        << <<5, [x |-> 3, b |-> FALSE]>>,
				           [ name |-> "B",
				             location |->
				                 [ beginLine |-> 11,
				                   beginColumn |-> 6,
				                   endLine |-> 13,
				                   endColumn |-> 18,
				                   module |-> "CodeplexBug8" ] ],
				           <<6, [x |-> 4, b |-> TRUE]>> >>,
				        << <<6, [x |-> 4, b |-> TRUE]>>,
				           [ name |-> "A",
				             location |->
				                 [ beginLine |-> 6,
				                   beginColumn |-> 6,
				                   endLine |-> 9,
				                   endColumn |-> 19,
				                   module |-> "CodeplexBug8" ] ],
				           <<7, [x |-> 4, b |-> FALSE]>> >>,
				        << <<7, [x |-> 4, b |-> FALSE]>>,
				           [ name |-> "B",
				             location |->
				                 [ beginLine |-> 11,
				                   beginColumn |-> 6,
				                   endLine |-> 13,
				                   endColumn |-> 18,
				                   module |-> "CodeplexBug8" ] ],
				           <<8, [x |-> 5, b |-> TRUE]>> >>,
				        << <<8, [x |-> 5, b |-> TRUE]>>,
				           [ name |-> "B",
				             location |->
				                 [ beginLine |-> 11,
				                   beginColumn |-> 6,
				                   endLine |-> 13,
				                   endColumn |-> 18,
				                   module |-> "CodeplexBug8" ] ],
				           <<8, [x |-> 5, b |-> TRUE]>> >> } ]
	      /\ ToTrace(CounterExample) =
		    	      << [x |-> 1, b |-> FALSE],
					   [x |-> 2, b |-> TRUE],
					   [x |-> 2, b |-> FALSE],
					   [x |-> 3, b |-> TRUE],
					   [x |-> 3, b |-> FALSE],
					   [x |-> 4, b |-> TRUE],
					   [x |-> 4, b |-> FALSE],
					   [x |-> 5, b |-> TRUE] >> 
=============================================================================
\* Modification History
\* Created Wed Mar 25 21:34:22 CET 2015 by markus
