---------------------------- MODULE Age_Channel ----------------------------

EXTENDS Integers, TLC


CONSTANT Messages,    (* All messages sent by correct processes. *)
         Boxes        (* Every message is put into a box which has information
                          about how long this message have been in transit. *) 
       

VARIABLES inTransit,  (* All messages are in transit. *)
          inDelivery  (* inDelivery contains messages which are delivered
                          to a process p_i in this transition. *)


(* Pack a message into a box with its age which shows how long a message
    have been in transit. *)
Pack_WaitingTime(msgs) == { [ content |-> m, age |-> 0 ] : m \in msgs }

(*  - Unpack boxes to get messages. Ages is not delivered. 
    - Those messages are delivered to a process in this transition. *)
Unpack(boxes) == { m.content : m \in boxes } 

(* Initialization *)
Init ==  
  /\ inTransit = {}   (* No boxes are in transit. *)
  /\ inDelivery = {}  (* No messages are delivered. *)


(* Pack a set msgs of messages with ages and put them in transit *)
Pickup(msgs) == 
  /\ inTransit' = inTransit \cup Pack_WaitingTime(msgs)
  /\ inDelivery' = {}  


(*  - Non-deterministically choose some boxes and deliver associated messages to rcver. 
    - Messages which are delivered are removed from inTransit. *)
Deliver(rcver) ==
  \E boxes \in SUBSET inTransit :
      /\ \A box \in boxes : box.content.to = rcver
      /\ inDelivery' = Unpack(boxes)
      /\ inTransit' = inTransit \ boxes

               
(*  - Every message in transit attains a new age at every tick of the environmental clock. 
    - Recall that we don't directly specify the environmental clock  in this encoding way.
      At every tick of the global clock, we only increase ages of boxes in transit.  
    - We can keep inDelivery unchanged. However, I set inDelivery' an empty set because it 
      makes an execution path more (human) readable, at least for me.  *)               
AttainAge ==
  /\ inTransit' = { [ content |-> package.content, age |-> package.age + 1 ]  : 
                        package \in inTransit }
  /\ inDelivery' = {}  
  
(* Type invariant for inTransit and inDelivery. *)
TypeOK ==
  /\ inTransit \subseteq Boxes
  /\ inDelivery \subseteq Messages 


=============================================================================
\* Modification History
\* Last modified Mon Jun 11 13:30:42 CEST 2018 by tthai
\* Created Thu Jun 07 09:30:18 CEST 2018 by tthai
