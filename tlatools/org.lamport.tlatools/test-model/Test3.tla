---------- MODULE Test3 -----------

(* This spec originates from an email conversation between Leslie and Yuan in 2009 *)

EXTENDS Naturals, TLC, TLCExt
VARIABLE x

Init == x=0

Next == IF x=0 THEN x' \in {1, 2}
        ELSE x' = 0

Spec == Init /\ [][Next]_x /\ WF_x(Next)

Prop1 ==  <>[](x#1) \/ <>[](x#2)

PostCondition ==
	/\ TLCSet(42, TLCGet("generated"))
	/\ \/ CounterExample = [state|->{},action|->{}] 
	   \/ /\ ToTrace(CounterExample) = <<[x |-> 0], [x |-> 1], [x |-> 0], [x |-> 2]>>
	   
	      /\ CounterExample =
			[ action |->
			      { << <<1, [x |-> 0]>>,
			           [ name |-> "Next",
			             location |->
			                 [ beginLine |-> 10,
			                   beginColumn |-> 9,
			                   endLine |-> 11,
			                   endColumn |-> 19,
			                   module |-> "Test3" ] ],
			           <<2, [x |-> 1]>> >>,
			        << <<2, [x |-> 1]>>,
			           [ name |-> "Next",
			             location |->
			                 [ beginLine |-> 10,
			                   beginColumn |-> 9,
			                   endLine |-> 11,
			                   endColumn |-> 19,
			                   module |-> "Test3" ] ],
			           <<3, [x |-> 0]>> >>,
			        << <<3, [x |-> 0]>>,
			           [ name |-> "Next",
			             location |->
			                 [ beginLine |-> 10,
			                   beginColumn |-> 9,
			                   endLine |-> 11,
			                   endColumn |-> 19,
			                   module |-> "Test3" ] ],
			           <<4, [x |-> 2]>> >>,
			        << <<4, [x |-> 2]>>,
			           [ name |-> "Next",
			             location |->
			                 [ beginLine |-> 10,
			                   beginColumn |-> 9,
			                   endLine |-> 11,
			                   endColumn |-> 19,
			                   module |-> "Test3" ] ],
			           <<1, [x |-> 0]>> >> },
			  state |->
			      {<<1, [x |-> 0]>>, <<2, [x |-> 1]>>, <<3, [x |-> 0]>>, <<4, [x |-> 2]>>} ]
	
===================================
