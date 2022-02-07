---- MODULE Github710a ----
EXTENDS TLC, TLCExt
VARIABLE x
vars == <<x>>

Init == x = FALSE

Next == x' \in BOOLEAN 

Spec == 
    /\ Init
    /\ [][Next]_vars
    \* /\ WF_x(Next)

StateConstraint ==
    TRUE

\* This is property to check
AtMostOnce == [](x => [](~x => []~x)) \* G(x => G(~x => G~x))

AtMostOnceEquiv == [](~x \/ [](x \/ []~x)) \* G(~x \/ G(x \/ G~x))

PostCondition ==
	/\ TLCSet(42, TLCGet("generated"))
	/\ ToTrace(CounterExample) = <<[x |-> FALSE], [x |-> TRUE], [x |-> FALSE], [x |-> TRUE]>>
	/\ CounterExample =
				[ action |->
			      { << <<1, [x |-> FALSE]>>,
			           [ name |-> "Next",
			             location |->
			                 [ beginLine |-> 8,
			                   beginColumn |-> 9,
			                   endLine |-> 8,
			                   endColumn |-> 22,
			                   module |-> "Github710a" ] ],
			           <<2, [x |-> TRUE]>> >>,
			        << <<2, [x |-> TRUE]>>,
			           [ name |-> "Next",
			             location |->
			                 [ beginLine |-> 8,
			                   beginColumn |-> 9,
			                   endLine |-> 8,
			                   endColumn |-> 22,
			                   module |-> "Github710a" ] ],
			           <<3, [x |-> FALSE]>> >>,
			        << <<3, [x |-> FALSE]>>,
			           [ name |-> "Next",
			             location |->
			                 [ beginLine |-> 8,
			                   beginColumn |-> 9,
			                   endLine |-> 8,
			                   endColumn |-> 22,
			                   module |-> "Github710a" ] ],
			           <<4, [x |-> TRUE]>> >> },
			  state |->
			      { <<1, [x |-> FALSE]>>,
			        <<2, [x |-> TRUE]>>,
			        <<3, [x |-> FALSE]>>,
			        <<4, [x |-> TRUE]>> } ]
====
