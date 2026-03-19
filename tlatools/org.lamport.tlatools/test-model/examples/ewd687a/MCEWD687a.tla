---- MODULE MCEWD687a ----
EXTENDS EWD687a, TLC, TLCExt

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
L, P1, P2, P3
----

\* MV CONSTANT definitions Procs
const_1633116534008310000 == 
{L, P1, P2, P3}
----

\* CONSTANT definitions @modelParameterConstants:1Edges
const_1633116534008311000 == 
{<<L, P1>>, <<P1, P2>>, <<P1, P2>>, <<P2, P1>>, <<P2,P3>>}
----

\* CONSTANT definitions @modelParameterConstants:2Leader
const_1633116534008312000 == 
L
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1633116534008313000 ==
\A e \in Edges : msgs[e] < 3 /\ acks[e] < 3 /\ sentUnacked[e] < 2 /\ rcvdUnacked[e] < 2

LeaderPermanentlyActive == <>[][Terminated]_vars

PostCondition ==
   CounterExample =
   [ action |->
      { << << 1,
              [ msgs |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                acks |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                sentUnacked |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                rcvdUnacked |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                active |->
                    (L :> TRUE @@ P1 :> FALSE @@ P2 :> FALSE @@ P3 :> FALSE),
                upEdge |-> (P1 :> <<>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >>,
           [ name |-> "SendMsg",
             location |->
                 [ beginLine |-> 298,
                   beginColumn |-> 15,
                   endLine |-> 302,
                   endColumn |-> 64,
                   module |-> "EWD687a" ],
             context |-> [p |-> L],
             parameters |-> <<"p">> ],
           << 2,
              [ msgs |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                acks |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                sentUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                rcvdUnacked |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                active |->
                    (L :> TRUE @@ P1 :> FALSE @@ P2 :> FALSE @@ P3 :> FALSE),
                upEdge |-> (P1 :> <<>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >> >>,
        << << 2,
              [ msgs |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                acks |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                sentUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                rcvdUnacked |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                active |->
                    (L :> TRUE @@ P1 :> FALSE @@ P2 :> FALSE @@ P3 :> FALSE),
                upEdge |-> (P1 :> <<>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >>,
           [ name |-> "RcvMsg",
             location |->
                 [ beginLine |-> 368,
                   beginColumn |-> 19,
                   endLine |-> 376,
                   endColumn |-> 52,
                   module |-> "EWD687a" ],
             context |-> [p |-> P1],
             parameters |-> <<"p">> ],
           << 3,
              [ msgs |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                acks |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                sentUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                rcvdUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                active |->
                    (L :> TRUE @@ P1 :> TRUE @@ P2 :> FALSE @@ P3 :> FALSE),
                upEdge |->
                    (P1 :> <<L, P1>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >> >>,
        << << 3,
              [ msgs |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                acks |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                sentUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                rcvdUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                active |->
                    (L :> TRUE @@ P1 :> TRUE @@ P2 :> FALSE @@ P3 :> FALSE),
                upEdge |-> (P1 :> <<L, P1>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >>,
           [ name |-> "Idle",
             location |->
                 [ beginLine |-> 385,
                   beginColumn |-> 12,
                   endLine |-> 386,
                   endColumn |-> 72,
                   module |-> "EWD687a" ],
             context |-> [p |-> L],
             parameters |-> <<"p">> ],
           << 4,
              [ msgs |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                acks |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                sentUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                rcvdUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                active |->
                    (L :> FALSE @@ P1 :> TRUE @@ P2 :> FALSE @@ P3 :> FALSE),
                upEdge |->
                    (P1 :> <<L, P1>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >> >>,
        << << 4,
              [ msgs |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                acks |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                sentUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                rcvdUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                active |->
                    (L :> FALSE @@ P1 :> TRUE @@ P2 :> FALSE @@ P3 :> FALSE),
                upEdge |-> (P1 :> <<L, P1>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >>,
           [ name |-> "SendMsg",
             location |->
                 [ beginLine |-> 298,
                   beginColumn |-> 15,
                   endLine |-> 302,
                   endColumn |-> 64,
                   module |-> "EWD687a" ],
             context |-> [p |-> P1],
             parameters |-> <<"p">> ],
           << 5,
              [ msgs |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 1 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                acks |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                sentUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 1 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                rcvdUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                active |->
                    (L :> FALSE @@ P1 :> TRUE @@ P2 :> FALSE @@ P3 :> FALSE),
                upEdge |->
                    (P1 :> <<L, P1>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >> >>,
        << << 5,
              [ msgs |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 1 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                acks |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                sentUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 1 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                rcvdUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                active |->
                    (L :> FALSE @@ P1 :> TRUE @@ P2 :> FALSE @@ P3 :> FALSE),
                upEdge |-> (P1 :> <<L, P1>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >>,
           [ name |-> "RcvMsg",
             location |->
                 [ beginLine |-> 368,
                   beginColumn |-> 19,
                   endLine |-> 376,
                   endColumn |-> 52,
                   module |-> "EWD687a" ],
             context |-> [p |-> P2],
             parameters |-> <<"p">> ],
           << 6,
              [ msgs |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                acks |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                sentUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 1 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                rcvdUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 1 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                active |->
                    (L :> FALSE @@ P1 :> TRUE @@ P2 :> TRUE @@ P3 :> FALSE),
                upEdge |->
                    (P1 :> <<L, P1>> @@ P2 :> <<P1, P2>> @@ P3 :> <<>>) ] >> >>,
        << << 6,
              [ msgs |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                acks |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                sentUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 1 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                rcvdUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 1 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                active |->
                    (L :> FALSE @@ P1 :> TRUE @@ P2 :> TRUE @@ P3 :> FALSE),
                upEdge |->
                    (P1 :> <<L, P1>> @@ P2 :> <<P1, P2>> @@ P3 :> <<>>) ] >>,
           [ name |-> "Idle",
             location |->
                 [ beginLine |-> 385,
                   beginColumn |-> 12,
                   endLine |-> 386,
                   endColumn |-> 72,
                   module |-> "EWD687a" ],
             context |-> [p |-> P2],
             parameters |-> <<"p">> ],
           << 7,
              [ msgs |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                acks |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                sentUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 1 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                rcvdUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 1 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                active |->
                    (L :> FALSE @@ P1 :> TRUE @@ P2 :> FALSE @@ P3 :> FALSE),
                upEdge |->
                    (P1 :> <<L, P1>> @@ P2 :> <<P1, P2>> @@ P3 :> <<>>) ] >> >>,
        << << 7,
              [ msgs |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                acks |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                sentUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 1 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                rcvdUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 1 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                active |->
                    (L :> FALSE @@ P1 :> TRUE @@ P2 :> FALSE @@ P3 :> FALSE),
                upEdge |->
                    (P1 :> <<L, P1>> @@ P2 :> <<P1, P2>> @@ P3 :> <<>>) ] >>,
           [ name |-> "SendAck",
             location |->
                 [ beginLine |-> 336,
                   beginColumn |-> 15,
                   endLine |-> 354,
                   endColumn |-> 58,
                   module |-> "EWD687a" ],
             context |-> [p |-> P2],
             parameters |-> <<"p">> ],
           << 8,
              [ msgs |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                acks |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 1 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                sentUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 1 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                rcvdUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                active |->
                    (L :> FALSE @@ P1 :> TRUE @@ P2 :> FALSE @@ P3 :> FALSE),
                upEdge |->
                    (P1 :> <<L, P1>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >> >>,
        << << 8,
              [ msgs |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                acks |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 1 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                sentUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 1 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                rcvdUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                active |->
                    (L :> FALSE @@ P1 :> TRUE @@ P2 :> FALSE @@ P3 :> FALSE),
                upEdge |-> (P1 :> <<L, P1>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >>,
           [ name |-> "RcvAck",
             location |->
                 [ beginLine |-> 311,
                   beginColumn |-> 19,
                   endLine |-> 314,
                   endColumn |-> 68,
                   module |-> "EWD687a" ],
             context |-> [p |-> P1],
             parameters |-> <<"p">> ],
           << 4,
              [ msgs |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                acks |->
                    ( <<L, P1>> :> 0 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                sentUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                rcvdUnacked |->
                    ( <<L, P1>> :> 1 @@
                      <<P1, P2>> :> 0 @@
                      <<P2, P1>> :> 0 @@
                      <<P2, P3>> :> 0 ),
                active |->
                    (L :> FALSE @@ P1 :> TRUE @@ P2 :> FALSE @@ P3 :> FALSE),
                upEdge |->
                    (P1 :> <<L, P1>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >> >> },
  state |->
      { << 1,
           [ msgs |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             acks |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             sentUnacked |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             rcvdUnacked |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             active |->
                 (L :> TRUE @@ P1 :> FALSE @@ P2 :> FALSE @@ P3 :> FALSE),
             upEdge |-> (P1 :> <<>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >>,
        << 2,
           [ msgs |->
                 ( <<L, P1>> :> 1 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             acks |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             sentUnacked |->
                 ( <<L, P1>> :> 1 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             rcvdUnacked |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             active |->
                 (L :> TRUE @@ P1 :> FALSE @@ P2 :> FALSE @@ P3 :> FALSE),
             upEdge |-> (P1 :> <<>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >>,
        << 3,
           [ msgs |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             acks |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             sentUnacked |->
                 ( <<L, P1>> :> 1 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             rcvdUnacked |->
                 ( <<L, P1>> :> 1 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             active |-> (L :> TRUE @@ P1 :> TRUE @@ P2 :> FALSE @@ P3 :> FALSE),
             upEdge |-> (P1 :> <<L, P1>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >>,
        << 4,
           [ msgs |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             acks |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             sentUnacked |->
                 ( <<L, P1>> :> 1 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             rcvdUnacked |->
                 ( <<L, P1>> :> 1 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             active |->
                 (L :> FALSE @@ P1 :> TRUE @@ P2 :> FALSE @@ P3 :> FALSE),
             upEdge |-> (P1 :> <<L, P1>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >>,
        << 5,
           [ msgs |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 1 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             acks |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             sentUnacked |->
                 ( <<L, P1>> :> 1 @@
                   <<P1, P2>> :> 1 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             rcvdUnacked |->
                 ( <<L, P1>> :> 1 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             active |->
                 (L :> FALSE @@ P1 :> TRUE @@ P2 :> FALSE @@ P3 :> FALSE),
             upEdge |-> (P1 :> <<L, P1>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >>,
        << 6,
           [ msgs |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             acks |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             sentUnacked |->
                 ( <<L, P1>> :> 1 @@
                   <<P1, P2>> :> 1 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             rcvdUnacked |->
                 ( <<L, P1>> :> 1 @@
                   <<P1, P2>> :> 1 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             active |-> (L :> FALSE @@ P1 :> TRUE @@ P2 :> TRUE @@ P3 :> FALSE),
             upEdge |->
                 (P1 :> <<L, P1>> @@ P2 :> <<P1, P2>> @@ P3 :> <<>>) ] >>,
        << 7,
           [ msgs |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             acks |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             sentUnacked |->
                 ( <<L, P1>> :> 1 @@
                   <<P1, P2>> :> 1 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             rcvdUnacked |->
                 ( <<L, P1>> :> 1 @@
                   <<P1, P2>> :> 1 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             active |->
                 (L :> FALSE @@ P1 :> TRUE @@ P2 :> FALSE @@ P3 :> FALSE),
             upEdge |->
                 (P1 :> <<L, P1>> @@ P2 :> <<P1, P2>> @@ P3 :> <<>>) ] >>,
        << 8,
           [ msgs |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             acks |->
                 ( <<L, P1>> :> 0 @@
                   <<P1, P2>> :> 1 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             sentUnacked |->
                 ( <<L, P1>> :> 1 @@
                   <<P1, P2>> :> 1 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             rcvdUnacked |->
                 ( <<L, P1>> :> 1 @@
                   <<P1, P2>> :> 0 @@
                   <<P2, P1>> :> 0 @@
                   <<P2, P3>> :> 0 ),
             active |->
                 (L :> FALSE @@ P1 :> TRUE @@ P2 :> FALSE @@ P3 :> FALSE),
             upEdge |-> (P1 :> <<L, P1>> @@ P2 :> <<>> @@ P3 :> <<>>) ] >> } ]
   
=============================================================================
\* Modification History
\* Created Fri Oct 01 12:28:54 PDT 2021 by lamport
