---------------------- MODULE MCLiveInternalMemory -------------------------
(***************************************************************************)
(* This is a module used for running TLC to check the specification LISpec *)
(* of LiveInternalMemory.  We need to tell TLC the values of the constant  *)
(* operators Send and Reply.  We define operators MCSend and MCReply and   *)
(* use the configuration file to tell TLC to substitute these operators    *)
(* for Send and Reply.  We also define MCInitMemInt, which is substituted  *)
(* for InitMemInt.                                                         *)
(*                                                                         *)
(* This module is identical to module MCInternalMemory                     *)
(* from folder CachingMemory, except it EXTENDS module LiveInternalMemory  *)
(* instead of InternalMemory.                                              *)
(***************************************************************************)

EXTENDS LiveInternalMemory, TLC, TLCExt

(***************************************************************************)
(* The operator Send is used in specifications in conjuncts of the form    *)
(*                                                                         *)
(* (+)  Send(p, d, memInt, memInt')                                        *)
(*                                                                         *)
(* to specify the new value of memInt.  For TLC to handle such a           *)
(* conjunct, the definition of Send must make (+) equal something of the   *)
(* form                                                                    *)
(*                                                                         *)
(*   memInt' = ...                                                         *)
(*                                                                         *)
(* (A similar observation holds for Reply.)  We define Send so that (+)    *)
(* equals                                                                  *)
(*                                                                         *)
(*   memInt' = <<p, d>>                                                    *)
(*                                                                         *)
(* If we were doing serious model checking, we might try to reduce         *)
(* the state space by letting the value of memInt remain constant,         *)
(* so we would define Send so that (+) equals                              *)
(*                                                                         *)
(*   memInt' = memInt.                                                     *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt)  ==  newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) ==  newMemInt = <<p, d>>

(***************************************************************************)
(* We define MCInitMemInt, the set of initial values of memInt, to contain *)
(* the single element <<p, NoVal>>, for an arbitrary processor p.          *)
(***************************************************************************)
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

AlwaysBusy == \A p \in Proc : []<>(ctl[p] = "busy")

CONSTANT p1, p2, a1, a2, a3, v1, v2

PostCondition ==
   CounterExample = 
   [ action |->
      { << << 1,
              [ ctl |-> (p1 :> "rdy" @@ p2 :> "rdy"),
                memInt |-> <<p1, NoVal>>,
                mem |-> (a1 :> v1 @@ a2 :> v1 @@ a3 :> v1),
                buf |-> (p1 :> NoVal @@ p2 :> NoVal) ] >>,
           [ name |-> "Req",
             location |->
                 [ beginLine |-> 15,
                   beginColumn |-> 11,
                   endLine |-> 20,
                   endColumn |-> 26,
                   module |-> "InternalMemory" ],
             context |-> [p |-> p2],
             parameters |-> <<"p">> ],
           << 2,
              [ ctl |-> (p1 :> "rdy" @@ p2 :> "busy"),
                memInt |-> <<p2, [val |-> v1, op |-> "Wr", adr |-> a2]>>,
                mem |-> (a1 :> v1 @@ a2 :> v1 @@ a3 :> v1),
                buf |->
                    ( p1 :> NoVal @@
                      p2 :> [val |-> v1, op |-> "Wr", adr |-> a2] ) ] >> >>,
        << << 2,
              [ ctl |-> (p1 :> "rdy" @@ p2 :> "busy"),
                memInt |-> <<p2, [val |-> v1, op |-> "Wr", adr |-> a2]>>,
                mem |-> (a1 :> v1 @@ a2 :> v1 @@ a3 :> v1),
                buf |->
                    ( p1 :> NoVal @@
                      p2 :> [val |-> v1, op |-> "Wr", adr |-> a2] ) ] >>,
           [ name |-> "Do",
             location |->
                 [ beginLine |-> 23,
                   beginColumn |-> 3,
                   endLine |-> 31,
                   endColumn |-> 21,
                   module |-> "InternalMemory" ],
             context |-> [p |-> p2],
             parameters |-> <<"p">> ],
           << 3,
              [ ctl |-> (p1 :> "rdy" @@ p2 :> "done"),
                memInt |-> <<p2, [val |-> v1, op |-> "Wr", adr |-> a2]>>,
                mem |-> (a1 :> v1 @@ a2 :> v1 @@ a3 :> v1),
                buf |-> (p1 :> NoVal @@ p2 :> NoVal) ] >> >>,
        << << 3,
              [ ctl |-> (p1 :> "rdy" @@ p2 :> "done"),
                memInt |-> <<p2, [val |-> v1, op |-> "Wr", adr |-> a2]>>,
                mem |-> (a1 :> v1 @@ a2 :> v1 @@ a3 :> v1),
                buf |-> (p1 :> NoVal @@ p2 :> NoVal) ] >>,
           [ name |-> "Rsp",
             location |->
                 [ beginLine |-> 33,
                   beginColumn |-> 11,
                   endLine |-> 36,
                   endColumn |-> 35,
                   module |-> "InternalMemory" ],
             context |-> [p |-> p2],
             parameters |-> <<"p">> ],
           << 4,
              [ ctl |-> (p1 :> "rdy" @@ p2 :> "rdy"),
                memInt |-> <<p2, NoVal>>,
                mem |-> (a1 :> v1 @@ a2 :> v1 @@ a3 :> v1),
                buf |-> (p1 :> NoVal @@ p2 :> NoVal) ] >> >>,
        << << 4,
              [ ctl |-> (p1 :> "rdy" @@ p2 :> "rdy"),
                memInt |-> <<p2, NoVal>>,
                mem |-> (a1 :> v1 @@ a2 :> v1 @@ a3 :> v1),
                buf |-> (p1 :> NoVal @@ p2 :> NoVal) ] >>,
           [ name |-> "Req",
             location |->
                 [ beginLine |-> 15,
                   beginColumn |-> 11,
                   endLine |-> 20,
                   endColumn |-> 26,
                   module |-> "InternalMemory" ],
             context |-> [p |-> p2],
             parameters |-> <<"p">> ],
           << 2,
              [ ctl |-> (p1 :> "rdy" @@ p2 :> "busy"),
                memInt |-> <<p2, [val |-> v1, op |-> "Wr", adr |-> a2]>>,
                mem |-> (a1 :> v1 @@ a2 :> v1 @@ a3 :> v1),
                buf |->
                    ( p1 :> NoVal @@
                      p2 :> [val |-> v1, op |-> "Wr", adr |-> a2] ) ] >> >> },
  state |->
      { << 1,
           [ ctl |-> (p1 :> "rdy" @@ p2 :> "rdy"),
             memInt |-> <<p1, NoVal>>,
             mem |-> (a1 :> v1 @@ a2 :> v1 @@ a3 :> v1),
             buf |-> (p1 :> NoVal @@ p2 :> NoVal) ] >>,
        << 2,
           [ ctl |-> (p1 :> "rdy" @@ p2 :> "busy"),
             memInt |-> <<p2, [val |-> v1, op |-> "Wr", adr |-> a2]>>,
             mem |-> (a1 :> v1 @@ a2 :> v1 @@ a3 :> v1),
             buf |->
                 ( p1 :> NoVal @@
                   p2 :> [val |-> v1, op |-> "Wr", adr |-> a2] ) ] >>,
        << 3,
           [ ctl |-> (p1 :> "rdy" @@ p2 :> "done"),
             memInt |-> <<p2, [val |-> v1, op |-> "Wr", adr |-> a2]>>,
             mem |-> (a1 :> v1 @@ a2 :> v1 @@ a3 :> v1),
             buf |-> (p1 :> NoVal @@ p2 :> NoVal) ] >>,
        << 4,
           [ ctl |-> (p1 :> "rdy" @@ p2 :> "rdy"),
             memInt |-> <<p2, NoVal>>,
             mem |-> (a1 :> v1 @@ a2 :> v1 @@ a3 :> v1),
             buf |-> (p1 :> NoVal @@ p2 :> NoVal) ] >> } ]
=============================================================================

