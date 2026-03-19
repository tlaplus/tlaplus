--------------------------------- MODULE ACP_SB --------------------------------
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>

\* `^Atomic Committment Protocol^' with Simple Broadcast primitive (ACP-SB)
\* From:
\* `^Sape Mullender^', editor.  Distributed Systems.
\* Chapter 6: Non-Blocking Atomic Commitment, by `^\"O. Babao\u{g}lu and S. Toueg.^'
\* 1993.

\*******************************************************************************
\* Synchronous communication has been replaced with (implicit) asynchronous communication.
\* Failures are detected "magically" instead or relying on timeouts.
\*
\* This version of the protocol uses a "simple broadcast" where a broadcast is simply a 
\* series of messages sent, possibly interrupted by a failure.  Consequently, this algorithm
\* is "non terminating" and property AC5 does not hold.
\*******************************************************************************

CONSTANTS
  participants,             \* set of participants
  yes, no,                  \* vote
  undecided, commit, abort, \* decision
  waiting,                  \* coordinator state wrt a participant
  notsent                   \* broadcast state wrt a participant

VARIABLES
  participant, \* participants (N)
  coordinator  \* coordinator  (1)

--------------------------------------------------------------------------------

TypeInvParticipant  == participant \in  [
                         participants -> [
                           vote      : {yes, no}, 
                           alive     : BOOLEAN, 
                           decision  : {undecided, commit, abort},
                           faulty    : BOOLEAN,
                           voteSent  : BOOLEAN
                         ]
                       ]

TypeInvCoordinator == coordinator \in  [
                        request   : [participants -> BOOLEAN],
                        vote      : [participants -> {waiting, yes, no}],
                        broadcast : [participants -> {commit, abort, notsent}],
                        decision  : {commit, abort, undecided},
                        alive     : BOOLEAN,
                        faulty    : BOOLEAN
                      ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

--------------------------------------------------------------------------------

\* Initially:
\* All the participants:
\*  have a yes/no vote
\*  are alive and not faulty
\*  have not sent in their votes yet
\*  are undecided about final decision

\* The coordinator:
\*  has not sent vote requests yet
\*  has not recieved votes from any participant
\*  is alive and not faulty
\*  has not sent broadcast messages to any participant
\*  is undecided about final decision

InitParticipant == participant \in [
                     participants -> [
                       vote     : {yes, no},
                       alive    : {TRUE},
                       decision : {undecided},
                       faulty   : {FALSE},
                       voteSent : {FALSE}
                     ]
                   ]

InitCoordinator == coordinator \in [
                     request   : [participants -> {FALSE}],
                     vote      : [participants -> {waiting}],
                     alive     : {TRUE},
                     broadcast : [participants -> {notsent}],
                     decision  : {undecided},
                     faulty    : {FALSE}
                   ]       

Init == InitParticipant /\ InitCoordinator

--------------------------------------------------------------------------------
\* COORDINATOR STATEMENTS

\* request(i):
\* IF
\*   coordinator is alive
\*   request for vote has not been sent to participant i
\* THEN `~ why isn't THEN left-justified? ~'
\*   request for vote is sent to participant i

request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request =
                   [@ EXCEPT ![i] = TRUE]
                 ]
              /\ UNCHANGED<<participant>>


\* getVote(i):
\* IF
\*   coordinator is alive
\*   coordinator is still undecided
\*   coordinator has sent request for votes to all participants
\*   coordinator is waiting to receive a vote from participant i
\*   participant i has sent the vote message
\* THEN
\*   the coordinator can record the vote of participant i

getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = 
                   [@ EXCEPT ![i] = participant[i].vote]
                 ]
              /\ UNCHANGED<<participant>>


\* detectFault(i):
\* IF
\*   coordinator is alive
\*   coordinator is still undecided
\*   coordinator has sent request for votes to all participants
\*   coordinator is waiting for vote from participant i
\*   participant i has died without sending its vote
\* THEN
\*   coordinator times out on participant i and decides to abort

detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED<<participant>>


\* makeDecision:
\* IF
\*   coordinator is alive
\*   coordinator is undecided
\*   coordinator has received votes from all participants
\* THEN
\*   IF
\*     all votes are yes
\*   THEN
\*     coordinator decides commit
\*   ELSE
\*     coordinator decides abort

makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
                      /\ coordinator' = [coordinator EXCEPT !.decision = commit]
                   \/ /\ \E j \in participants : coordinator.vote[j] = no
                      /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                /\ UNCHANGED<<participant>>


\* coordBroadcast(i) (simple broadcast):
\* IF 
\*   coordinator is alive
\*   coordinator has made a decision
\*   coordinator has not sent the decision to participant i
\* THEN
\*   coordinator sends its decision to participant i 

coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast = 
                          [@ EXCEPT ![i] = coordinator.decision]
                        ]
                     /\ UNCHANGED<<participant>>


\* coordDie:
\* IF 
\*   coordinator is alive
\* THEN
\*   coordinator dies
\*   coordinator is now faulty

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED<<participant>>

------------------------------------------------------------------------------

\* PARTICIPANT STATEMENTS 

\* sendVote(i):
\* IF 
\*   participant is alive
\*   participant has received a request for vote
\* THEN
\*   participant sends vote

sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i] = 
                    [@ EXCEPT !.voteSent = TRUE]
                  ]
               /\ UNCHANGED<<coordinator>>


\* abortOnVote(i):
\* IF
\*   participant is alive
\*   participant is undecided
\*   participant has sent its vote to the coordinator
\*   participant's vote is no
\* THEN
\*   participant decides (unilaterally) to abort

abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i] = 
                       [@ EXCEPT !.decision = abort]
                     ]
                  /\ UNCHANGED<<coordinator>>


\* abortOnTimeoutRequest(i):
\* IF
\*   participant is alive
\*   participant is still undecided
\*   coordinator has died without sending request for vote
\* THEN
\*   participant decides (unilaterally) to abort

abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i] = 
                                 [@ EXCEPT !.decision = abort]
                               ]
                            /\ UNCHANGED<<coordinator>>


\* decide(i):
\* IF
\*   participant is alive
\*   participant is undecided
\*   participant has recieved decision from the coordinator
\* THEN
\*   participant decides according to decision from coordinator
\*

decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i] = 
                  [@ EXCEPT !.decision = coordinator.broadcast[i]]
                ]
             /\ UNCHANGED<<coordinator>>


\* parDie(i):
\* IF
\*   participant is alive
\* THEN
\*   participant dies and is now faulty

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i] = 
                  [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]
                ]
             /\ UNCHANGED<<coordinator>>

-------------------------------------------------------------------------------

\* FOR N PARTICIPANTS

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

parProgN == \E i \in participants : parDie(i) \/ parProg(i)


coordProgA(i) ==  request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)

coordProgN == coordDie \/ coordProgB


progN == parProgN \/ coordProgN

\* Death transitions are left outside of fairness

fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)


Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

--------------------------------------------------------------------------------

\* CORRECTNESS SPECIFICATION

\*******************************************************************************
\* This specification follows the original paper, except that AC3 is stronger:
\* It forces participants to abort if one vote at least is NO (in the absence 
\* of failure).
\*
\* The specification is split between safety and liveness.
\*******************************************************************************

--------------------------------------------------------------------------------

\* SAFETY

\* All participants that decide reach the same decision
AC1 == [] \A i, j \in participants : 
          \/ participant[i].decision # commit 
          \/ participant[j].decision # abort

\* If any participant decides commit, then all participants must have votes YES
AC2 == [] (  (\E i \in participants : participant[i].decision = commit) 
          => (\A j \in participants : participant[j].vote = yes))

\* If any participant decides abort, then:
\*   at least one participant voted NO, or
\*   at least one participant is faulty, or
\*   coordinator is faulty
AC3_1 == [] (  (\E i \in participants : participant[i].decision = abort) 
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty)

\* Each participant decides at most once
AC4 == [] /\ (\A i \in participants : participant[i].decision = commit 
                                => [](participant[i].decision = commit))
          /\ (\A j \in participants : participant[j].decision = abort  
                                => [](participant[j].decision = abort))

--------------------------------------------------------------------------------

\* LIVENESS 
\* (stronger for AC3 than in the original paper)

AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E j \in participants : participant[j].faulty
            \/ coordinator.faulty

--------------------------------------------------------------------------------

\* (SOME) INTERMEDIATE PROPERTIES USED IN PROOFS

FaultyStable == /\ \A i \in participants : [](participant[i].faulty => []participant[i].faulty)
                /\ [](coordinator.faulty => [] coordinator.faulty)

VoteStable == \A i \in participants : 
                \/ [](participant[i].vote = yes)
                \/ [](participant[i].vote = no)

StrongerAC2 == [] (  (\E i \in participants : participant[i].decision = commit) 
                  => /\ (\A j \in participants : participant[j].vote = yes)
                     /\ coordinator.decision = commit)

StrongerAC3_1 == [] (  (\E i \in participants : participant[i].decision = abort) 
                    => \/ (\E j \in participants : participant[j].vote = no)
                       \/ /\ \E j \in participants : participant[j].faulty
                          /\ coordinator.decision = abort
                       \/ /\ coordinator.faulty
                          /\ coordinator.decision = undecided)

\* (AC1 follows from StrongerAC2 /\ StrongerAC3_1)

NoRecovery == [] /\ \A i \in participants : participant[i].alive <=> ~participant[i].faulty
                 /\ coordinator.alive <=> ~coordinator.faulty

--------------------------------------------------------------------------------

\* (SOME) INVALID PROPERTIES 

DecisionReachedNoFault == (\A i \in participants : participant[i].alive)
                          ~> (\A k \in participants : participant[k].decision # undecided)

AbortImpliesNoVote == [] (  (\E i \in participants : participant[i].decision = abort) 
                  => (\E j \in participants : participant[j].vote = no))

\* The following is the termination property that this SB algorithm doesn't have
AC5 == <> \A i \in participants : \/ participant[i].decision \in {abort, commit} 
                                  \/ participant[i].faulty

================================================================================