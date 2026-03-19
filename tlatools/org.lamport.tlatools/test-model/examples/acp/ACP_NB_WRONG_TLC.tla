--------------------------- MODULE ACP_NB_WRONG_TLC ----------------------------

\* Erroneous Non blocking Atomic Committment Protocol (ACP-NB)
\* The mistake is to deliver a broacast message locally *before* it has been
\* forwarded to other participants.
\* This protocol does not satisfy the consistency property AC1

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
\*   participant i has received a decision and has decided (it shouldn't have decided yet)
\*   participant i has not yet forwarded this decision to participant j
\* THEN
\*   participant i forwards the decision to participant j

forward(i,j) == /\ i # j
                /\ participant[i].alive
                /\ participant[i].decision # notsent
                /\ participant[i].forward[j] = notsent
                /\ participant' = [participant EXCEPT ![i] = 
                     [@ EXCEPT !.forward = 
                       [@ EXCEPT ![j] = participant[i].decision]
                     ]
                   ]
                /\ UNCHANGED<<coordinator>>


\* decideOnForward(i,j): participant i receives decision from participant j
\* IF
\*   participant i is alive
\*   participant i has yet to receive a decision
\*   participant j has forwarded its decision to participant i
\* THEN
\*   participant i decides in accordance with participant j's decision (it should only predecide)

decideOnForward(i,j) == /\ i # j
                        /\ participant[i].alive
                        /\ participant[i].decision = undecided
                        /\ participant[j].forward[i] # notsent
                        /\ participant' = [participant EXCEPT ![i] = 
                             [@ EXCEPT !.decision = participant[j].forward[i]]
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

parProgNB(i,j) == \/ parProg(i)
                  \/ forward(i,j) 
                  \/ decideOnForward(i,j) 
                  \/ abortOnTimeout(i) 

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
              /\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

================================================================================
