-------------------------- MODULE PaxosMadeSimple --------------------------
(***************************************************************************)
(* A specification of the algorithm described in "Paxos Made Simple",      *)
(* based on the specification found in:                                    *)
(* `^\url{research.microsoft.com/en-us/um/people/lamport/tla/PConProof.tla}^' *)
(***************************************************************************)
EXTENDS Integers, FiniteSets
-----------------------------------------------------------------------------

CONSTANT Value, Acceptor, Quorum

ASSUME QA == /\ \A Q \in Quorum : Q \subseteq Acceptor 
             /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 

(***************************************************************************)
(* Ballot numbers are the natural numbers.                                 *)
(***************************************************************************)                                                                     
Ballot ==  Nat

(***************************************************************************)
(* We are going to have a leader PlusCal process for each ballot and an    *)
(* acceptor PlusCal process for each acceptor (see the "process"           *)
(* definitions below).  A proposer that proposes a value in ballot n is    *)
(* modeled by the leader PlusCal process identified by n.  Thus a single   *)
(* proposer is modeled by multiple leader PlusCal processes, one for each  *)
(* ballot in which the proposer proposes a value.  We use the ballot       *)
(* numbers and the acceptors themselves as the identifiers for these       *)
(* processes and we assume that the set of ballots and the set of          *)
(* acceptors are disjoint.  For good measure, we also assume that -1 is    *)
(* not an acceptor, although that is probably not necessary.               *)
(***************************************************************************)
ASSUME BallotAssump == (Ballot \cup {-1}) \cap Acceptor = {}

(***************************************************************************)
(* We define None to be an unspecified value that is not in the set Value. *)
(***************************************************************************)
None == CHOOSE v : v \notin Value
 
(***************************************************************************)
(* This is a message-passing algorithm, so we begin by defining the set    *)
(* Message of all possible messages.  The messages are explained below     *)
(* with the actions that send them.  A message m with m.type = "1a" is     *)
(* called a 1a message, and similarly for the other message types.         *)
(***************************************************************************)
Message ==      [type : {"1a"}, bal : Ballot]
           \cup [type : {"1b"}, acc : Acceptor, bal : Ballot,
                 mbal : Ballot \cup {-1}, mval : Value \cup {None}]
           \cup [type : {"2a"}, bal : Ballot, val : Value]
           \cup [type : {"2b"}, acc : Acceptor, bal : Ballot, val : Value]

-----------------------------------------------------------------------------


(***************************************************************************)
(* The algorithm is easiest to understand in terms of the set msgs of all  *)
(* messages that have ever been sent.  A more accurate model would use one *)
(* or more variables to represent the messages actually in transit, and it *)
(* would include actions representing message loss and duplication as well *)
(* as message receipt.                                                     *)
(*                                                                         *)
(* In the current spec, there is no need to model message loss explicitly. *)
(* The safety part of the spec says only what messages may be received and *)
(* does not assert that any message actually is received.  Thus, there is  *)
(* no difference between a lost message and one that is never received.    *)
(* The liveness property of the spec will make it clear what messages must *)
(* be received (and hence either not lost or successfully retransmitted if *)
(* lost) to guarantee progress.                                            *)
(*                                                                         *)
(* Another advantage of maintaining the set of all messages that have ever *)
(* been sent is that it allows us to define the state function `votes'     *)
(* that implements the variable of the same name in the voting algorithm   *)
(* without having to introduce a history variable.                         *)
(***************************************************************************)

(***********

--algorithm PCon {
  variables maxBal  = [a \in Acceptor |-> -1] ,
            maxVBal = [a \in Acceptor |-> -1] ,
            maxVVal = [a \in Acceptor |-> None] ,
            msgs = {}
  define {
    sentMsgs(t, b) == {m \in msgs : (m.type = t) /\ (m.bal = b)}

    Max(xs, LessEq(_,_)) ==
        CHOOSE x \in xs : \A y \in xs : LessEq(y,x)    
    
    HighestAcceptedValue(Q1bMessages) ==
        Max(Q1bMessages, LAMBDA m1,m2 : m1.mbal \leq m2.mbal).mval
    
    (***********************************************************************)
    (* We define ShowsSafeAt so that ShowsSafeAt(Q, b, v) is true for a    *)
    (* quorum Q iff the msgs contained in ballot-b 1b messages from the    *)
    (* acceptors in Q show that v is safe at b.                            *)
    (***********************************************************************)
    ShowsSafeAt(Q, b, v) ==
      LET Q1b == {m \in sentMsgs("1b", b) : m.acc \in Q}
      IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a 
          /\ \/ \A m \in Q1b : m.mbal = -1
             \/ v = HighestAcceptedValue(Q1b)
    }
 
  (*************************************************************************)
  (* We describe each action as a macro.                                   *)
  (*                                                                       *)
  (* In PlusCal, `self' is used by convention to designate the id of the   *)
  (* PlusCal process being defined.                                        *)
  (*                                                                       *)
  (* The leader for ballot `self' can execute a Phase1a() action, which    *)
  (* sends the ballot `self' 1a message (remember that for leader PlusCal  *)
  (* processes, the identifier of the process is the ballot number).       *)
  (*************************************************************************)
  macro Phase1a() { msgs := msgs \cup {[type |-> "1a", bal |-> self]} ; }
  
  (*************************************************************************)
  (* Acceptor `self' can perform a Phase1b(b) action, which is enabled iff *)
  (* b > maxBal[self].  The action sets maxBal[self] to b (therefore       *)
  (* promising never to accept proposals with ballot lower than b: see     *)
  (* Phase2b below) and sends a phase 1b message to the leader of ballot b *)
  (* containing the values of maxVBal[self] and maxVVal[self].             *)
  (*************************************************************************)
  macro Phase1b(b) {
    when (b > maxBal[self]) /\ (sentMsgs("1a", b) # {});
    maxBal[self] := b;
    msgs := msgs \cup {[type |-> "1b", acc |-> self, bal |-> b, 
                        mbal |-> maxVBal[self], mval |-> maxVVal[self]]} ;
   }

  (*************************************************************************)
  (* The ballot `self' leader can perform a Phase2a(v) action, sending a   *)
  (* 2a message for value v, if it has not already sent a 2a message (for  *)
  (* this ballot) and it can determine that v is safe at ballot `self'.    *)
  (*************************************************************************)
  macro Phase2a(v) {
    when /\ sentMsgs("2a", self) = {}
         /\ \E Q \in Quorum : ShowsSafeAt(Q, self, v);
    msgs := msgs \cup {[type |-> "2a", bal |-> self, val |-> v]};
   }

  (*************************************************************************)
  (* The Phase2b(b) action is executed by acceptor `self' in response to a *)
  (* ballot-b 2a message.  Note this action can be executed multiple times *)
  (* by the acceptor, but after the first one, all subsequent executions   *)
  (* are stuttering steps that do not change the value of any variable.    *)
  (* Note that the acceptor `self' does not accept any proposal with a     *)
  (* ballot lower than b, as per its promise to the leader of ballot b in  *)
  (* Phase1b above.                                                        *)
  (*                                                                       *)
  (* Note that there is not need to update maxBal.                         *)
  (*************************************************************************)
  macro Phase2b(b) {
    when b \geq maxBal[self] ;
    with (m \in sentMsgs("2a", b)) {
      if (b \geq maxVBal[self]) {
        maxVBal[self] := b;
        maxVVal[self] := m.val
      };
      msgs := msgs \cup {[type |-> "2b", acc |-> self, 
                             bal |-> b, val |-> m.val]}
    }
   }
   
  (*************************************************************************)
  (* An acceptor performs the body of its `while' loop as a single atomic  *)
  (* action by nondeterministically choosing a ballot in which its Phase1b *)
  (* or Phase2b action is enabled and executing that enabled action.  If   *)
  (* no such action is enabled, the acceptor does nothing.                 *)
  (*************************************************************************)
  process (acceptor \in Acceptor) {
    acc: while (TRUE) { 
            with (b \in Ballot) { either Phase1b(b) or Phase2b(b)  } }
   }

  (*************************************************************************)
  (* The leader of a ballot nondeterministically chooses one of its        *)
  (* actions that is enabled (and the argument for which it is enabled)    *)
  (* and performs it atomically.  It does nothing if none of its actions   *)
  (* is enabled.                                                           *)
  (*************************************************************************)
  process (leader \in Ballot) {
    ldr: while (TRUE) {
          either Phase1a()
          or     with (v \in Value) { Phase2a(v) }
         }
   }

}

**********)

(***************************************************************************)
(* Below is the translation (obtained automatically) of the PlusCal        *)
(* algorithm above.                                                        *)
(***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES maxBal, maxVBal, maxVVal, msgs

(* define statement *)
sentMsgs(t, b) == {m \in msgs : (m.type = t) /\ (m.bal = b)}

Max(xs, LessEq(_,_)) ==
    CHOOSE x \in xs : \A y \in xs : LessEq(y,x)

HighestAcceptedValue(Q1bMessages) ==
    Max(Q1bMessages, LAMBDA m1,m2 : m1.mbal \leq m2.mbal).mval






ShowsSafeAt(Q, b, v) ==
  LET Q1b == {m \in sentMsgs("1b", b) : m.acc \in Q}
  IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
      /\ \/ \A m \in Q1b : m.mbal = -1
         \/ v = HighestAcceptedValue(Q1b)


vars == << maxBal, maxVBal, maxVVal, msgs >>

ProcSet == (Acceptor) \cup (Ballot)

Init == (* Global variables *)
        /\ maxBal = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVVal = [a \in Acceptor |-> None]
        /\ msgs = {}

acceptor(self) == \E b \in Ballot:
                    \/ /\ (b > maxBal[self]) /\ (sentMsgs("1a", b) # {})
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ msgs' = (msgs \cup {[type |-> "1b", acc |-> self, bal |-> b,
                                               mbal |-> maxVBal[self], mval |-> maxVVal[self]]})
                       /\ UNCHANGED <<maxVBal, maxVVal>>
                    \/ /\ b \geq maxBal[self]
                       /\ \E m \in sentMsgs("2a", b):
                            /\ IF b \geq maxVBal[self]
                                  THEN /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
                                       /\ maxVVal' = [maxVVal EXCEPT ![self] = m.val]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED << maxVBal, maxVVal >>
                            /\ msgs' = (msgs \cup {[type |-> "2b", acc |-> self,
                                                       bal |-> b, val |-> m.val]})
                       /\ UNCHANGED maxBal

leader(self) == /\ \/ /\ msgs' = (msgs \cup {[type |-> "1a", bal |-> self]})
                   \/ /\ \E v \in Value:
                           /\ /\ sentMsgs("2a", self) = {}
                              /\ \E Q \in Quorum : ShowsSafeAt(Q, self, v)
                           /\ msgs' = (msgs \cup {[type |-> "2a", bal |-> self, val |-> v]})
                /\ UNCHANGED << maxBal, maxVBal, maxVVal >>

Next == (\E self \in Acceptor: acceptor(self))
           \/ (\E self \in Ballot: leader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

(***************************************************************************)
(* TypeOK is an invariant asserting that the variables are of the type     *)
(* that we expect.  We use it to catch trivial "coding" errors.            *)
(***************************************************************************)
TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVVal \in [Acceptor -> Value \cup {None}]
          /\ msgs \subseteq Message    
          
(***************************************************************************)
(* Chosen(b, v) is true when a quorum of acceptors have broadcasted a 2b   *)
(* message with the same value v in ballot b.  Note that a learner         *)
(* (learners are not modeled in this specification) ca learn v if and only *)
(* if Chosen(b, v) is true for some ballot b.                              *)
(***************************************************************************)
ChosenIn(b, v) ==
    \E Q \in Quorum : \A a \in Q : 
        \E m \in sentMsgs("2b", b) : 
            /\  m.acc = a
            /\  m.val = v
            
(***************************************************************************)
(* Chosen(v) is true when v has been chosen in some ballot.                *)
(***************************************************************************)            
Chosen(v) == \E b \in Ballot : ChosenIn(b,v)

(***************************************************************************)
(* The Agreement property of the consensus problem says that no two        *)
(* learners learn different values.  Since a learner can learn a value v   *)
(* if and only if Chosen(v) is true, the following Correctness property    *)
(* implies Agreement.                                                      *)
(***************************************************************************)
Correctness ==
    \A v1,v2 \in Value : Chosen(v1) /\ Chosen(v2) => v1 = v2

(***************************************************************************)
(* This theorem states that in every execution of the specification, the   *)
(* Correcntess property is always true.  Note that in the current form of  *)
(* the spec, this theorem is incorrect.  Use TLC to find an execution that *)
(* violates it.                                                            *)
(***************************************************************************)
THEOREM Spec => []Correctness

Votes == [a \in Acceptor |-> 
    [b \in Nat |-> IF \E  v \in Value : [type |-> "2b", bal |-> b, acc |-> a, val |-> v] \in msgs
        THEN CHOOSE v \in Value : [type |-> "2b", bal |-> b, acc |-> a, val |-> v] \in msgs
        ELSE <<>>]]

=============================================================================
\* Modification History
\* Last modified Fri Aug 04 16:16:29 PDT 2017 by nano
\* Created Thu Sep 03 22:58:03 EDT 2015 by nano
