------------------------------ MODULE Huang ------------------------------
\* https://en.wikipedia.org/wiki/Huang%27s_algorithm
EXTENDS Naturals, DyadicRationals, Sequences, SequencesExt, Functions

CONSTANTS Procs, Leader

ASSUME
    \* The leader is one of the processes.
    Leader \in Procs    

VARIABLES 
    active,
    weight,
    msgs

vars == <<active, weight, msgs>>

RECURSIVE Sum(_,_)
Sum(fun, set) ==
    IF set = {} THEN Zero
    ELSE LET p == CHOOSE p \in set: TRUE
         IN Add(FoldFunction(Add, Zero, fun[p]), Sum(fun, set \ {p}))

TypeOK ==
    /\ active \in [ Procs -> BOOLEAN ]
    /\ \A p \in Procs : 
            \A i \in 1..Len(msgs[p]) :
                IsDyadicRational(msgs[p][i])
    /\ \A p \in Procs : IsDyadicRational(weight[p])
    \* The sum of the weights of all processes and the messages in transit is always 1.
    /\ LET M == Sum(msgs, Procs)
       IN Add(FoldFunction(Add, Zero, weight), M) = One

----------------------------------------------------------------------------

Init ==
    \* All processes except the leader are idle.
    /\ active = [ p \in Procs |-> IF p = Leader THEN TRUE ELSE FALSE ]
    \* No weights have been "thrown" yet.
    /\ weight = [ p \in Procs |-> IF p = Leader THEN One ELSE Zero ]
    \* No messages have been sent yet.
    /\ msgs \in [ Procs -> {<<>>} ]

SendMsg(p) ==
    /\ active[p]
    \* This spec models a fully meshed network.
    /\ \E q \in Procs : 
           /\ weight' = [weight EXCEPT ![p] = Half(weight[p])]
           /\ msgs' = [msgs EXCEPT ![q] = Append(@, weight[p]')]
    /\ UNCHANGED <<active>>

RcvMsg(p) ==
    \* The order in which messages are received does not matter.
    \E i \in 1..Len(msgs[p]) :
        /\ active' = [active EXCEPT ![p] = TRUE]
        /\ weight' = [weight EXCEPT ![p] = Add(@, msgs[p][i])]
        /\ msgs' = [msgs EXCEPT ![p] = RemoveAt(@, i)]

Idle(p) ==
    /\ active[p] \* This enablement condition prevents an idle process to send a zero weight message.
    /\ active' = [active EXCEPT ![p] = FALSE]
    \* An idle process throws its weight back to leader.
    /\ msgs' = [msgs EXCEPT ![Leader] = Append(@, weight[p])]
    /\ weight' = [weight EXCEPT ![p] = Zero]
 
----------------------------------------------------------------------------

IdleLdr ==
    /\ active[Leader]
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ UNCHANGED <<weight, msgs>>

RcvLdr ==
    \* The order in which messages are received does not matter.
    \E i \in 1..Len(msgs[Leader]) :
        /\ weight' = [weight EXCEPT ![Leader] = Add(@, msgs[Leader][i])]
        /\ msgs' = [msgs EXCEPT ![Leader] = RemoveAt(@, i)]
        /\ UNCHANGED active

Next ==
    \/ \E p \in Procs : SendMsg(p)
    \/ \E p \in Procs \ {Leader} : RcvMsg(p) \/ Idle(p)
    \/ RcvLdr \/ IdleLdr

Spec ==
        /\ Init 
        /\ [][Next]_vars
        /\ WF_vars(RcvLdr)
        /\ WF_vars(IdleLdr)
        /\ \A p \in Procs \ {Leader}: WF_vars(RcvMsg(p))
        /\ \A p \in Procs \ {Leader}: WF_vars(Idle(p))

----------------------------------------------------------------------------
TerminationDetected ==
    /\ ~active[Leader]
    /\ weight[Leader] = One

Terminated ==
    \A p \in Procs : 
        /\ ~active[p] 
        /\ msgs[p] = <<>>

Safe == 
    [](TerminationDetected => []Terminated)

THEOREM Spec => Safe
               
Live == 
    Terminated ~> TerminationDetected

THEOREM Spec => Live

----------------------------------------------------------------------------

StateConstraint ==
    \* Prevent the weights from halving towards infinity.
    \A p \in Procs : weight[p].den <= 7

Alias ==
    [
        \* Pretty printing of error-trace states.
        active |-> {p \in Procs : active[p]},
        weights |-> [p \in { q \in Procs: weight[q] # Zero} 
                        |-> PrettyPrint(weight[p])],
        msgs |-> [p \in { q \in Procs: msgs[q] # <<>>} 
                        |-> [ i \in 1..Len(msgs[p]) |-> PrettyPrint(msgs[p][i])]]
    ]

===============================================================================
\* Modification History
\* Last modified Mon Dec 27 17:52:54 PST 2021 by Markus Kuppe
\* Created Sun Dec 26 01:36:40 PDT 2021 by Markus Kuppe
