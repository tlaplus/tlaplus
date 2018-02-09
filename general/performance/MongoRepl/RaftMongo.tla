--------------------------------- MODULE RaftMongo ---------------------------------
\* This is the formal specification for the Raft consensus algorithm in MongoDB

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
\* Candidate is not used, but this is fine.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

----
\* Global variables

\* The server's term number.
VARIABLE globalCurrentTerm

----
\* The following variables are all per server (functions with domain Server).

\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
serverVars == <<globalCurrentTerm, state>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
logVars == <<log>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<serverVars, logVars>>

----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LogTerm(i, index) == IF index = 0 THEN 0 ELSE log[i][index].term
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----
\* Define initial values for all variables

InitServerVars == /\ globalCurrentTerm = 1
                  /\ state             = [i \in Server |-> Follower]
InitLogVars == /\ log          = [i \in Server |-> << >>]
Init == /\ InitServerVars
        /\ InitLogVars

----
\* Message handlers
\* i = recipient, j = sender, m = message

AppendOplog(i, j) ==
    /\ Len(log[i]) < Len(log[j])
    /\ LastTerm(log[i]) = LogTerm(j, Len(log[i]))
    /\ log' = [log EXCEPT ![i] = Append(log[i], log[j][Len(log[i]) + 1])]
    /\ UNCHANGED <<serverVars>>

CanRollbackOplog(i, j) ==
    /\ Len(log[i]) > 0
    /\ \* The log with later term is more up-to-date
       LastTerm(log[i]) < LastTerm(log[j])
    /\
       \/ Len(log[i]) > Len(log[j])
       \* There seems no short-cut of OR clauses, so I have to specify the negative case
       \/ /\ Len(log[i]) <= Len(log[j])
          /\ LastTerm(log[i]) /= LogTerm(j, Len(log[i]))

RollbackOplog(i, j) ==
    /\ CanRollbackOplog(i, j)
    \* Rollback 1 oplog entry
    /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |-> log[i][index2]]
         IN log' = [log EXCEPT ![i] = new]
    /\ UNCHANGED <<serverVars>>


\* RollbackCommitted and NeverRollbackCommitted are not actions.
\* They are used for verification.
RollbackCommitted(i) ==
    LET
        \* The set of nodes that has log[me][logIndex] in their oplog
        Agree(me, logIndex) ==
            { node \in Server :
                /\ Len(log[node]) >= logIndex
                /\ LogTerm(me, logIndex) = LogTerm(node, logIndex) }
        IsCommitted(me, logIndex) ==
            /\ Agree(me, logIndex) \in Quorum
            \* If we comment out the following line, a replicated log entry from old primary will voilate the safety.
            \* [ P (2), S (), S ()]
            \* [ S (2), S (), P (3)]
            \* [ S (2), S (2), P (3)] !!! the log from term 2 shouldn't be considered as committed.
            /\ LogTerm(me, logIndex) = globalCurrentTerm
    IN  \E j \in Server:
        /\ CanRollbackOplog(i, j)
        /\ IsCommitted(i, Len(log[i]))

NeverRollbackCommitted ==
    \A i \in Server: ~RollbackCommitted(i)

\* i = the new primary node.
BecomePrimaryByMagic(i) ==
    LET notBehind(me, j) ==
            \/ LastTerm(log[me]) > LastTerm(log[j])
            \/ /\ LastTerm(log[me]) = LastTerm(log[j])
               /\ Len(log[me]) >= Len(log[j])
        ayeVoters(me) ==
            { index \in Server : notBehind(me, index) }
    IN /\ ayeVoters(i) \in Quorum
       /\ state' = [index \in Server |-> IF index = i THEN Leader ELSE Follower]
       /\ globalCurrentTerm' = globalCurrentTerm + 1
       /\ UNCHANGED <<logVars>>

\* Leader i receives a client request to add v to the log.
ClientWrite(i, v) ==
    /\ state[i] = Leader
    /\ LET entry == [term  |-> globalCurrentTerm,
                     value |-> v]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<serverVars>>

----
\* Defines how the variables may transition.
Next == /\
           \/ \E i,j \in Server : AppendOplog(i, j)
           \/ \E i,j \in Server : RollbackOplog(i, j)
           \/ \E i \in Server : BecomePrimaryByMagic(i)
           \/ \E i \in Server, v \in Value : ClientWrite(i, v)

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

===============================================================================
