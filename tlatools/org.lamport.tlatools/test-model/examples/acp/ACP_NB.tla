-------------------------------- MODULE ACP_NB ---------------------------------
\* Time-stamp: <10 Jun 2002 at 14:06:57 by charpov on berlioz.cs.unh.edu>

\* Non blocking Atomic Committment Protocol (ACP-NB)
\* The non blocking property AC5 is obtained by using a reliable broadcast 
\* implemented as follows:
\*   - upon reception of a broadcast message, this message is forwarded to all
\*     participants before it's delivered to the local site;
\*   - since participant i does not forward to itself, forward[i] is used to 
\*     store the decision before it's delivered (and becomes "decision")

EXTENDS ACP_SB

--------------------------------------------------------------------------------

\* Participants type is extended with a "forward" variable.  
\* Coordinator type is unchanged.

TypeInvParticipantNB  == participant \in  [
                           participants -> [
                             vote      : {yes, no}, 
                             alive     : BOOLEAN, 
                             decision  : {undecided, commit, abort},
                             faulty    : BOOLEAN,
                             voteSent  : BOOLEAN,
                             forward   : [ participants -> {notsent, commit, abort} ]
                           ]
                         ]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

--------------------------------------------------------------------------------

\* Initially, participants have not forwarded anything yet

InitParticipantNB == participant \in [
                       participants -> [
                         vote     : {yes, no},
                         alive    : {TRUE},
                         decision : {undecided},
                         faulty   : {FALSE},
                         voteSent : {FALSE},
                         forward  : [ participants -> {notsent} ]
                       ]
                     ]

InitNB == InitParticipantNB /\ InitCoordinator

--------------------------------------------------------------------------------

\* Participant statements that realize a better broadcast 

\* forward(i,j): forwarding of the predecision from participant i to participant j
\* IF
\*   particpant i is alive
\*   participant i has received a decision (stored in forward[i])
\*   participant i has not yet forwarded this decision to participant j
\* THEN
\*   participant i forwards the decision to participant j

forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].forward[i] # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] = 
                     [@ EXCEPT !.forward = 
                       [@ EXCEPT ![j] = participant[i].forward[i]]
                     ]
                   ]
                /\ UNCHANGED<<coordinator>>


\* preDecideOnForward(i,j): participant i receives decision from participant j
\* IF
\*   participant i is alive
\*   participant i has yet to receive a decision
\*   participant j has forwarded its decision to participant i
\* THEN
\*   participant i (pre)decides in accordance with participant j's decision

preDecideOnForward(i,j) == /\ i # j
                           /\ participant[i].alive
                           /\ participant[i].forward[i] = notsent
                           /\ participant[j].forward[i] # notsent
                           /\ participant' = [participant EXCEPT ![i] = 
                                [@ EXCEPT !.forward = 
                                  [@ EXCEPT ![i] = participant[j].forward[i]]
                                ]
                              ]
                           /\ UNCHANGED<<coordinator>>


\* preDecide(i): participant i receives decision from coordinator
\* IF
\*   participant i is alive
\*   participant i has yet to receive a decision
\*   coordinator has sent its decision to participant i
\* THEN
\*   participant i (pre)decides in accordance with coordinator's decision

preDecide(i) == /\ participant[i].alive
                /\ participant[i].forward[i] = notsent
                /\ coordinator.broadcast[i] # notsent
                /\ participant' = [participant EXCEPT ![i] = 
                     [@ EXCEPT !.forward =
                       [@ EXCEPT ![i] = coordinator.broadcast[i]]
                     ]
                   ]
                /\ UNCHANGED<<coordinator>>


\* decideNB(i): Actual decision, after predecision has been forwarded
\* IF
\*   participant i is alive
\*   participant i has forwarded its (pre)decision to all other participants
\* THEN
\*   participant i decides in accordance with it's predecision

decideNB(i) == /\ participant[i].alive
               /\ \A j \in participants : participant[i].forward[j] # notsent
               /\ participant' = [participant EXCEPT ![i] = 
                    [@ EXCEPT !.decision = participant[i].forward[i]]
                  ]
               /\ UNCHANGED<<coordinator>>


\* abortOnTimeout(i): conditions for a timeout are simulated
\* IF
\*  participant is alive and undecided and coordinator is not alive
\*  coordinator died before sending decision to all participants who are alive
\*  all dead participants died before forwarding decision to a participant who is alive
\* THEN
\*  decide abort

abortOnTimeout(i) == /\ participant[i].alive
                     /\ participant[i].decision = undecided
                     /\ ~coordinator.alive
                     /\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
                     /\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
                     /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                     /\ UNCHANGED<<coordinator>>

---------------------------------------------------------------------------------

\* FOR N PARTICIPANTS

parProgNB(i,j) == \/ sendVote(i) 
                  \/ abortOnVote(i)
                  \/ abortOnTimeoutRequest(i)
                  \/ forward(i,j) 
                  \/ preDecideOnForward(i,j) 
                  \/ abortOnTimeout(i) 
                  \/ preDecide(i) 
                  \/ decideNB(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

--------------------------------------------------------------------------------

\* (SOME) INVALID PROPERTIES 

AllCommit == \A i \in participants : <>(participant[i].decision = commit \/ participant[i].faulty)

AllAbort  == \A i \in participants : <>(participant[i].decision = abort  \/ participant[i].faulty)

AllCommitYesVotes == \A i \in participants :
                         \A j \in participants : participant[j].vote = yes
                     ~>  participant[i].decision = commit \/ participant[i].faulty \/ coordinator.faulty

================================================================================
