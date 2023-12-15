---------------------------- MODULE Github807 ---------------------------
EXTENDS Naturals, TLCExt
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
==============================================================================
---------------------------- CONFIG Github807 ----------------------------
SPECIFICATION Spec

INVARIANT IsNotTwo

POSTCONDITION PostCondition
===========================================================================
