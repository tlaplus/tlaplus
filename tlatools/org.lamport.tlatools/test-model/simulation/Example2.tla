------------------------------ MODULE Example2 ------------------------------
EXTENDS Integers, TLC, TLCExt

VARIABLE x

Init == x = 0

Next == x' = ( x + 1 ) % 10

Spec == Init /\ [][Next]_<<x>> /\ []<><<TRUE>>_<<x>> 

Liveness2 == <>(x = 11)

Alias == [ x |-> x, l |-> TLCGet("level") ]

PostCondition ==
	CounterExample =
		[ state |->
		      { <<1, [x |-> 0, l |-> 1]>>,
		        <<2, [x |-> 1, l |-> 2]>>,
		        <<3, [x |-> 2, l |-> 3]>>,
		        <<4, [x |-> 3, l |-> 4]>>,
		        <<5, [x |-> 4, l |-> 5]>>,
		        <<6, [x |-> 5, l |-> 6]>>,
		        <<7, [x |-> 6, l |-> 7]>>,
		        <<8, [x |-> 7, l |-> 8]>>,
		        <<9, [x |-> 8, l |-> 9]>>,
		        <<10, [x |-> 9, l |-> 10]>> },
		  action |->
		      { << <<1, [x |-> 0, l |-> 1]>>,
		           [ name |-> "Next",
		             location |->
		                 [ beginLine |-> 8,
		                   beginColumn |-> 9,
		                   endLine |-> 8,
		                   endColumn |-> 27,
		                   module |-> "Example2" ] ],
		           <<2, [x |-> 1, l |-> 2]>> >>,
		        << <<2, [x |-> 1, l |-> 2]>>,
		           [ name |-> "Next",
		             location |->
		                 [ beginLine |-> 8,
		                   beginColumn |-> 9,
		                   endLine |-> 8,
		                   endColumn |-> 27,
		                   module |-> "Example2" ] ],
		           <<3, [x |-> 2, l |-> 3]>> >>,
		        << <<3, [x |-> 2, l |-> 3]>>,
		           [ name |-> "Next",
		             location |->
		                 [ beginLine |-> 8,
		                   beginColumn |-> 9,
		                   endLine |-> 8,
		                   endColumn |-> 27,
		                   module |-> "Example2" ] ],
		           <<4, [x |-> 3, l |-> 4]>> >>,
		        << <<4, [x |-> 3, l |-> 4]>>,
		           [ name |-> "Next",
		             location |->
		                 [ beginLine |-> 8,
		                   beginColumn |-> 9,
		                   endLine |-> 8,
		                   endColumn |-> 27,
		                   module |-> "Example2" ] ],
		           <<5, [x |-> 4, l |-> 5]>> >>,
		        << <<5, [x |-> 4, l |-> 5]>>,
		           [ name |-> "Next",
		             location |->
		                 [ beginLine |-> 8,
		                   beginColumn |-> 9,
		                   endLine |-> 8,
		                   endColumn |-> 27,
		                   module |-> "Example2" ] ],
		           <<6, [x |-> 5, l |-> 6]>> >>,
		        << <<6, [x |-> 5, l |-> 6]>>,
		           [ name |-> "Next",
		             location |->
		                 [ beginLine |-> 8,
		                   beginColumn |-> 9,
		                   endLine |-> 8,
		                   endColumn |-> 27,
		                   module |-> "Example2" ] ],
		           <<7, [x |-> 6, l |-> 7]>> >>,
		        << <<7, [x |-> 6, l |-> 7]>>,
		           [ name |-> "Next",
		             location |->
		                 [ beginLine |-> 8,
		                   beginColumn |-> 9,
		                   endLine |-> 8,
		                   endColumn |-> 27,
		                   module |-> "Example2" ] ],
		           <<8, [x |-> 7, l |-> 8]>> >>,
		        << <<8, [x |-> 7, l |-> 8]>>,
		           [ name |-> "Next",
		             location |->
		                 [ beginLine |-> 8,
		                   beginColumn |-> 9,
		                   endLine |-> 8,
		                   endColumn |-> 27,
		                   module |-> "Example2" ] ],
		           <<9, [x |-> 8, l |-> 9]>> >>,
		        << <<9, [x |-> 8, l |-> 9]>>,
		           [ name |-> "Next",
		             location |->
		                 [ beginLine |-> 8,
		                   beginColumn |-> 9,
		                   endLine |-> 8,
		                   endColumn |-> 27,
		                   module |-> "Example2" ] ],
		           <<10, [x |-> 9, l |-> 10]>> >>,
		        << <<10, [x |-> 9, l |-> 10]>>,
		           [ name |-> "Next",
		             location |->
		                 [ beginLine |-> 8,
		                   beginColumn |-> 9,
		                   endLine |-> 8,
		                   endColumn |-> 27,
		                   module |-> "Example2" ] ],
		           <<1, [x |-> 0, l |-> 1]>> >> } ]

=============================================================================