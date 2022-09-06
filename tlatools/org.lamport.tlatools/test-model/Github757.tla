---------------------------- MODULE Github757 ----------------------------
EXTENDS Naturals, TLC, TLCExt

VARIABLE x
vars == <<x>>

Init == x = 1

Next == x' = x + 1

Spec == 
    /\ Init
    /\ [][Next]_vars

Inv == x < 2

PostCondition ==
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
		                   module |-> "Github757" ] ],
		           <<2, [x |-> 2]>> >> },
		  state |-> {<<1, [x |-> 1]>>, <<2, [x |-> 2]>>} ]

==========================================================================
---------------------------- CONFIG Github757 ----------------------------
SPECIFICATION Spec
INVARIANT Inv
POSTCONDITION PostCondition
==========================================================================
