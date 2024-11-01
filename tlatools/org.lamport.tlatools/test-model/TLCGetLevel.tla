--------------------------- MODULE TLCGetLevel ----------------------------
EXTENDS Integers, TLC

VARIABLES x, y, yb, z

ASSUME(TLCGet("level") = 0)

Init ==
   /\ TLCGet("level") = 0
   /\ yb = TLCGet("level")
   /\ x = 0
   /\ y = TLCGet("level")
   /\ z = 1

Next == 
   /\ TLCGet("level") > 0
   /\ Assert(TLCGet("level") + 1 = TLCGet("level")', "Failure pre next-state")
   /\ yb' = TLCGet("level")
   /\ x < 3 
   /\ x' = x + 1
   /\ y' = TLCGet("level")
   /\ z' = TLCGet("level")'
   /\ Assert(TLCGet("level") + 1 = TLCGet("level")', "Failure post next-state")

Inv ==
    /\ y = yb
    /\ z = TLCGet("level")
    /\ x + 1 = TLCGet("level")
    \* /\ TLCGet("level") < 4  \* To trigger a safety violation.

ActionConstraint ==
    /\ Assert(TLCGet("level") + 1 = TLCGet("level")', "Failure action constraint")

StateConstraint ==
    /\ TLCGet("level") \in 1..4

Prop ==
    /\ <>[](x = 2)
    /\ [][y' > y /\ yb' > yb /\ TLCGet("level") + 1 = TLCGet("level")']_<<x, y, yb, z>>

PostCondition ==
    TLCGet("spec") = [ impliedinits |-> {},
                invariants |->
                    { [ coverage |-> [count |-> 4],
                        name |-> "Inv",
                        location |->
                            [ beginLine |-> 26,
                                beginColumn |-> 5,
                                endLine |-> 28,
                                endColumn |-> 30,
                                module |-> "TLCGetLevel" ] ] },
                impliedtemporals |->
                    { [ name |-> "UnnamedAction",
                        location |->
                            [ beginLine |-> 38,
                                beginColumn |-> 8,
                                endLine |-> 38,
                                endColumn |-> 18,
                                module |-> "TLCGetLevel" ] ] },
                temporals |-> {},
                actions |->
                    { [ coverage |-> [generated |-> 6, distinct |-> 3],
                        name |-> "Next",
                        location |->
                            [ beginLine |-> 16,
                                beginColumn |-> 4,
                                endLine |-> 23,
                                endColumn |-> 79,
                                module |-> "TLCGetLevel" ] ] },
                inits |->
                    { [ coverage |-> [generated |-> 2, distinct |-> 2],
                        name |-> "Init",
                        location |->
                            [ beginLine |-> 9,
                                beginColumn |-> 4,
                                endLine |-> 13,
                                endColumn |-> 11,
                                module |-> "TLCGetLevel" ] ] },
                variables |->
                    { [ coverage |-> [distinct |-> 3],
                        name |-> "x",
                        location |->
                            [ beginLine |-> 4,
                                beginColumn |-> 11,
                                endLine |-> 4,
                                endColumn |-> 11,
                                module |-> "TLCGetLevel" ] ],
                        [ coverage |-> [distinct |-> 3],
                        name |-> "y",
                        location |->
                            [ beginLine |-> 4,
                                beginColumn |-> 14,
                                endLine |-> 4,
                                endColumn |-> 14,
                                module |-> "TLCGetLevel" ] ],
                        [ coverage |-> [distinct |-> 3],
                        name |-> "yb",
                        location |->
                            [ beginLine |-> 4,
                                beginColumn |-> 17,
                                endLine |-> 4,
                                endColumn |-> 18,
                                module |-> "TLCGetLevel" ] ],
                        [ coverage |-> [distinct |-> 3],
                        name |-> "z",
                        location |->
                            [ beginLine |-> 4,
                                beginColumn |-> 21,
                                endLine |-> 4,
                                endColumn |-> 21,
                                module |-> "TLCGetLevel" ] ] },
                actionconstraints |->
                    { [ name |-> "ActionConstraint",
                        location |->
                            [ beginLine |-> 32,
                                beginColumn |-> 5,
                                endLine |-> 32,
                                endColumn |-> 82,
                                module |-> "TLCGetLevel" ] ] },
                constraints |->
                    { [ name |-> "StateConstraint",
                        location |->
                            [ beginLine |-> 35,
                                beginColumn |-> 5,
                                endLine |-> 35,
                                endColumn |-> 31,
                                module |-> "TLCGetLevel" ] ] } ]

=============================================================================
