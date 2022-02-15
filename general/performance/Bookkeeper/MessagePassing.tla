--------------------------- MODULE MessagePassing ---------------------------
EXTENDS FiniteSets, FiniteSetsExt, Sequences, SequencesExt, Integers, TLC

CONSTANTS AddEntryRequestMessage,
          AddEntryResponseMessage,
          FenceRequestMessage,
          FenceResponseMessage,
          ReadRequestMessage,
          ReadResponseMessage

VARIABLES messages

(***************************************************************************)
(* Message Passing                                                         *)
(*                                                                         *)
(* Messages are represented by a funcion of MSG -> Delivery Count.         *)
(* Each message sent is modelled as both delivered and lost via            *)
(* existential quantification. When a message is processed, the delivery   *)
(* count is decremented.                                                   *)
(* When a message is lost, the delivery count is set to -1 to              *)
(* differentiate it from a processed message. Time outs are enabled by     *)
(* detecting messages with a del count of -1. Once a time out has been     *)
(* acted upon, the -1 count is cleared (set to 0) so the time out is not   *)
(* triggered more than once.                                               *)
(* Resending messages is not currently modelled but is supported by simply *)
(* incrementing the delivery count.                                        *)
(*                                                                         *)
(* NOTE: There are no ordering guarantees of message receipt for any given *)
(*       actor. So a bookie may be delivered an AddEntryRequest from the   *)
(*       writer first, then a Read request from the 2nd client after that, *)
(*       but the bookie process the read request first, and the add second.*)
(***************************************************************************)

ReadTimeoutForBookie(msgs, cid, bookie) ==
    \E msg \in DOMAIN msgs :
        /\ msgs[msg] = -1
        /\ msg.bookie = bookie
        /\ msg.cid = cid
        /\ msg.type \in {ReadRequestMessage, ReadResponseMessage}

WriteTimeoutForBookie(msgs, cid, bookie, recovery) ==
    \E msg \in DOMAIN msgs :
        /\ msgs[msg] = -1
        /\ msg.bookie = bookie
        /\ msg.cid = cid
        /\ msg.type \in {AddEntryRequestMessage, AddEntryResponseMessage}
        /\ msg.recovery = recovery


ReadTimeoutCount(cid, ensemble, recovery) ==
    IF \E b \in ensemble : ReadTimeoutForBookie(messages, cid, b)
    THEN Cardinality({ b \in ensemble : ReadTimeoutForBookie(messages, cid, b)})
    ELSE 0

ClearWriteTimeout(cid, bookies, recovery) ==
    messages' = [m \in DOMAIN messages |-> IF /\ (m.type = AddEntryRequestMessage \/ m.type = AddEntryResponseMessage)
                                              /\ m.bookie \in bookies
                                              /\ m.cid = cid
                                              /\ m.recovery = recovery
                                              /\ messages[m] = -1
                                           THEN 0
                                           ELSE messages[m]]

\* Ignore the undelivered messages that match.
\* This is a state space optimization that makes these messages
\* never get delivered
IgnoreFurtherReadResponses(msg, ensemble) ==
    messages' = [m \in DOMAIN messages |-> IF msg = m
                                           THEN 0
                                           ELSE IF /\ m.bookie \in ensemble
                                                   /\ m.cid = msg.cid
                                                   /\ (m.type = ReadRequestMessage \/ m.type = ReadResponseMessage)
                                                   /\ messages[m] = 1
                                                THEN 0
                                                ELSE messages[m]]

DelCountOf(msg, counts) ==
    LET pair == CHOOSE c \in counts : c[1] = msg
    IN pair[2]

\* Send a set of messages only if none have been previously sent
\* In any given step, a random subset of these messages are lost (including none)
\* The TLA+ is simply choosing a delivery count for each message that
\* TLC will explore exhaustively.
SendMessagesToEnsemble(msgs) ==
    /\ \A msg \in msgs : msg \notin DOMAIN messages
    /\ LET possible_del_counts == { s \in SUBSET (msgs \X {-1, 1}) :
                                        /\ Cardinality(s) = Cardinality(msgs)
                                        /\ \A msg \in msgs : \E s1 \in s : s1[1] = msg
                                  }
       IN
            \E counts \in possible_del_counts :
                LET msgs_to_send == [m \in msgs |-> DelCountOf(m, counts)]
                IN messages' = messages @@ msgs_to_send

\* Send a message only if the message has not already been sent
SendMessage(msg) ==
    /\ msg \notin DOMAIN messages
    /\ \E delivered_count \in {-1,1} :
        messages' = messages @@ (msg :> delivered_count)

\* Mark one message as processed and send a new message
ProcessedOneAndSendAnother(received_msg, send_msg) ==
    /\ received_msg \in DOMAIN messages
    /\ send_msg \notin DOMAIN messages
    /\ messages[received_msg] >= 1
    /\ \E delivered_count \in {-1, 1} :
        /\ messages' = [messages EXCEPT ![received_msg] = @-1] @@ (send_msg :> delivered_count)

\* Mark one message as processed
MessageProcessed(msg) ==
    /\ msg \in DOMAIN messages
    /\ messages[msg] >= 1
    /\ messages' = [messages EXCEPT ![msg] = @ - 1]

\* The message is of this type and has been delivered to the recipient
ReceivableMessageOfType(msgs, msg, message_type) ==
    /\ msg.type = message_type
    /\ msgs[msg] >= 1
    
ReceivableRequest(msgs, msg) ==
    /\ msg.type \in { AddEntryRequestMessage,
                      FenceRequestMessage,
                      ReadRequestMessage }
    /\ msgs[msg] >= 1    

ReceivableResponse(msgs, msg) ==
    /\ msg.type \in { AddEntryResponseMessage,
                      FenceResponseMessage,
                      ReadResponseMessage }
    /\ msgs[msg] >= 1 

IsEarliestMsg(msg) ==
    ~\E msg2 \in DOMAIN messages :
        /\ ReceivableMessageOfType(messages, msg2, msg.type)
        /\ msg2.recovery = msg.recovery
        /\ msg2.entry.id < msg.entry.id
        /\ msg2.cid = msg.cid
        /\ msg2.bookie = msg.bookie

=============================================================================
\* Modification History
\* Last modified Mon Dec 06 10:02:52 CET 2021 by GUNMETAL
\* Last modified Mon Nov 23 09:37:09 CET 2020 by jvanlightly
\* Created Mon Nov 23 09:19:26 CET 2020 by jvanlightly
