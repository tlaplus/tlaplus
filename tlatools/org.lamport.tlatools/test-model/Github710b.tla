---- MODULE Github710b ----
EXTENDS Naturals, TLC, TLCExt

VARIABLE x
vars == <<x>>

Init == x = 1

Next == x' = x + 1

Spec == 
    /\ Init
    /\ [][Next]_vars
    \* /\ WF_x(Next)

StateConstraint ==
    x < 5

AtMostOnce == [](x > 1 => [](x > 2)) \* violated by x = 2

PostCondition ==
	/\ TLCSet(42, TLCGet("generated"))
	/\ ToTrace(CounterExample) = <<[x |-> 1], [x |-> 2]>>
	/\ CounterExample =
			[ action |->
		      { << <<1, [x |-> 1]>>,
		           [ name |-> "Next",
		             location |->
		                 [ beginLine |-> 9,
		                   beginColumn |-> 9,
		                   endLine |-> 9,
		                   endColumn |-> 18,
		                   module |-> "Github710b" ] ],
		           <<2, [x |-> 2]>> >> },
		  state |-> {<<1, [x |-> 1]>>, <<2, [x |-> 2]>>} ]
			
====
