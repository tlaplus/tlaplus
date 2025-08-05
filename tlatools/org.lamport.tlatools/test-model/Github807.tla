---------------------------- MODULE Github807 ---------------------------
EXTENDS Naturals, TLCExt, TLC
VARIABLE x

Init == x = 0

Add(d,n) ==
    /\ x' = x + d
    /\ x' <= 10

Next(r) ==
    LET d == IF x = x THEN 1 ELSE 1
    IN Add(d,r)

IsNotTwo == x # 2

Spec == Init /\ [][Next(1)]_x

PostCondition ==
       /\ CounterExample =
                       [ action |->
                             { << <<1, [x |-> 0]>>,
                                  [ name |-> "Add",
                                    location |->
                                        [ beginLine |-> 13,
                                          beginColumn |-> 8,
                                          endLine |-> 13,
                                          endColumn |-> 15,
                                          module |-> "Github807" ] ],
                                  <<2, [x |-> 1]>> >>,
                               << <<2, [x |-> 1]>>,
                                  [ name |-> "Add",
                                    location |->
                                        [ beginLine |-> 13,
                                          beginColumn |-> 8,
                                          endLine |-> 13,
                                          endColumn |-> 15,
                                          module |-> "Github807" ] ],
                                  <<3, [x |-> 2]>> >> },
                         state |-> {<<1, [x |-> 0]>>, <<2, [x |-> 1]>>, <<3, [x |-> 2]>>} ]
       /\ TLCGet("spec") =
				       [ impliedinits |-> {}, impliedactions |-> {},
				  invariants |->
				      { [ name |-> "IsNotTwo",
				          location |->
				              [ beginLine |-> 15,
				                beginColumn |-> 13,
				                endLine |-> 15,
				                endColumn |-> 17,
				                module |-> "Github807" ],
				          coverage |-> [count |-> 3] ] },
				  impliedtemporals |-> {},
				  temporals |-> {},
				  actions |->
				      { [ name |-> "Add",
				          location |->
				              [ beginLine |-> 13,
				                beginColumn |-> 8,
				                endLine |-> 13,
				                endColumn |-> 15,
				                module |-> "Github807" ],
				          coverage |-> [generated |-> 6, distinct |-> 2] ] },
				  inits |->
				      { [ name |-> "Init",
				          location |->
				              [ beginLine |-> 5,
				                beginColumn |-> 9,
				                endLine |-> 5,
				                endColumn |-> 13,
				                module |-> "Github807" ],
				          coverage |-> [generated |-> 3, distinct |-> 3] ] },
				  variables |->
				      { [ name |-> "x",
				          coverage |-> [distinct |-> 1],
				          location |->
				              [ beginLine |-> 3,
				                beginColumn |-> 10,
				                endLine |-> 3,
				                endColumn |-> 10,
				                module |-> "Github807" ] ] },
				  actionconstraints |-> {},
				  constraints |-> {} ]
==============================================================================
---------------------------- CONFIG Github807 ----------------------------
SPECIFICATION Spec

INVARIANT IsNotTwo

POSTCONDITION PostCondition
===========================================================================
