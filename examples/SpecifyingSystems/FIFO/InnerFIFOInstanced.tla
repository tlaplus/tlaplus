------------------------ MODULE InnerFIFOInstanced --------------------------
(***************************************************************************)
(* The current version of TLC does not handle the INSTANCE statement.      *)
(* (This omission will be rectified with TLC Version 2.)  This module is a *)
(* version of module InnerFIFO for use with TLC. The INSTANCE statements   *)
(* of module InnerFIFO have been removed and replaced by explicit          *)
(* definitions of the operators originally defined through instantiation.  *)
(***************************************************************************)

EXTENDS Naturals, Sequences
CONSTANT Message
VARIABLES in, out, q
-----------------------------------------------------------------------------
(***************************************************************************)
(* At this point, module InnerFIFO contains the two statements:            *)
(*                                                                         *)
(*    InChan  == INSTANCE Channel WITH Data <- Message, chan <- in         *)
(*    OutChan == INSTANCE Channel WITH Data <- Message, chan <- out        *)
(*                                                                         *)
(* We perform the instantiations below "by hand".  However, since "!"      *)
(* can't appear in an identifier name, we use "_" in its place.  For       *)
(* example, instead of adding the definition of `InChan!Init' to the       *)
(* current module, as does the first INSTANCE statement, we instead add    *)
(* the definition of `InChan_Init'.                                        *)
(***************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* Below are all the definitions from Channel, except with `in'            *)
(* substituted for `chan', with `Message' substituted for `Data', and with *)
(* "InChan_" prepended to the names of all defined symbols.                *)
(***************************************************************************)
InChan_TypeInvariant  ==  in \in [val : Message,  rdy : {0, 1},  ack : {0, 1}]

InChan_Init  ==  /\ InChan_TypeInvariant
                 /\ in.ack = in.rdy 

InChan_Send(d) ==  /\ in.rdy = in.ack
                   /\ in' = [in EXCEPT !.val = d, !.rdy = 1 - @]

InChan_Rcv     ==  /\ in.rdy # in.ack
                   /\ in' = [in EXCEPT !.ack = 1 - @]

InChan_Next  ==  (\E d \in Message : InChan_Send(d)) \/ InChan_Rcv

InChan_Spec  ==  InChan_Init /\ [][InChan_Next]_in
-----------------------------------------------------------------------------
(***************************************************************************)
(* Below are all the definitions from Channel, except with `out'            *)
(* substituted for `chan', with `Message' substituted for `Data', and with *)
(* "OutChan_" prepended to the names of all defined symbols.               *)
(***************************************************************************)
OutChan_TypeInvariant  ==  out \in [val : Message,  rdy : {0, 1},  ack : {0, 1}]

OutChan_Init  ==  /\ OutChan_TypeInvariant
                  /\ out.ack = out.rdy 

OutChan_Send(d) ==  /\ out.rdy = out.ack
                    /\ out' = [out EXCEPT !.val = d, !.rdy = 1 - @]

OutChan_Rcv     ==  /\ out.rdy # out.ack
                    /\ out' = [out EXCEPT !.ack = 1 - @]

OutChan_Next  ==  (\E d \in Message : OutChan_Send(d)) \/ OutChan_Rcv

OutChan_Spec  ==  OutChan_Init /\ [][OutChan_Next]_out
-----------------------------------------------------------------------------
(***************************************************************************)
(* The rest of the module is the same as module InnerFIFO, except that     *)
(* each "!" is replaced by "_".                                            *)
(***************************************************************************)
Init == /\ InChan_Init
        /\ OutChan_Init
        /\ q = << >>

TypeInvariant  ==  /\ InChan_TypeInvariant
                   /\ OutChan_TypeInvariant
                   /\ q \in Seq(Message)

SSend(msg)  ==  /\ InChan_Send(msg)       \* Send msg on channel `in'.
                /\ UNCHANGED <<out, q>>

BufRcv == /\ InChan_Rcv              \* Receive message from channel `in'.
          /\ q' = Append(q, in.val)  \*   and append it to tail of q.
          /\ UNCHANGED out

BufSend == /\ q # << >>               \* Enabled only if q is nonempty.
           /\ OutChan_Send(Head(q))   \* Send Head(q) on channel `out'
           /\ q' = Tail(q)            \*   and remove it from q.
           /\ UNCHANGED in

RRcv == /\ OutChan_Rcv          \* Receive message from channel `out'.
        /\ UNCHANGED <<in, q>>

Next == \/ \E msg \in Message : SSend(msg)
        \/ BufRcv
        \/ BufSend
        \/ RRcv 

Spec == Init /\ [][Next]_<<in, out, q>>
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================


