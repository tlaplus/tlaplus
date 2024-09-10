-------------------------- MODULE Github687fifo --------------------------
EXTENDS Naturals, Sequences

CONSTANT Endpoints, Messages, MaxSize

VARIABLE channel

Init ==  channel \in [Endpoints -> {<<>>}]

Write(endpoint, message) ==
    /\ Len(channel[endpoint]) /= MaxSize
    /\ channel' = [channel EXCEPT ![endpoint] = Append(@, message)]

Read(endpoint) ==
    /\ channel[endpoint] /= <<>>
    /\ channel' = [channel EXCEPT ![endpoint] = Tail(@)]

Next == 
  \E endpoint \in Endpoints:
    \/ Read(endpoint)
    \/ \E message \in Messages:
        Write(endpoint, message)

Spec == Init /\ [][Next]_channel

RefinedQueue(endpoint) == INSTANCE FIFO WITH
    queue <- channel[endpoint]

\* This didn't work because of parametric instantiation
Refinement == 
	\A endpoint \in Endpoints :
		RefinedQueue(endpoint)!Spec
===========================================================================

---------------------------- MODULE FIFO ----------------------------
EXTENDS Sequences

CONSTANT Messages

VARIABLE queue

Init == queue = <<>>

Put(message) == queue' = Append(queue, message)

Get ==
    /\ queue /= <<>>
    /\ queue' = Tail(queue)

Next ==
    \/ \E message \in Messages: Put(message)
    \/ Get

Spec == Init /\ [][Next]_queue
===========================================================================

-------------------------- CONFIG Github687fifo --------------------------
SPECIFICATION Spec
CONSTANTS
    Endpoints = { E0, E1 }
    Messages = { M0, M1}
    MaxSize = 2
PROPERTY Refinement
===========================================================================
