------------------------------- MODULE Voting ------------------------------- 
(***************************************************************************)
(* This is a high-level algorithm in which a set of processes              *)
(* cooperatively choose a value.                                           *)
(***************************************************************************)
EXTENDS Integers 
-----------------------------------------------------------------------------
CONSTANT Value,     \* The set of choosable values.
         Acceptor,  \* A set of processes that will choose a value.
         Quorum     \* The set of "quorums", where a quorum" is a 
                    \*   "large enough" set of acceptors

(***************************************************************************)
(* Here are the assumptions we make about quorums.                         *)
(***************************************************************************)
ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}  

THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
-----------------------------------------------------------------------------
(***************************************************************************)
(* Ballot is a set of "ballot numbers".  For simplicity, we let it be the  *)
(* set of natural numbers.  However, we write Ballot for that set to       *)
(* distinguish ballots from natural numbers used for other purposes.       *)
(***************************************************************************)
Ballot == Nat
-----------------------------------------------------------------------------
(***************************************************************************)
(* In the algorithm, each acceptor can cast one or more votes, where each  *)
(* vote cast by an acceptor has the form <<b, v>> indicating that the      *)
(* acceptor has voted for value v in ballot b.  A value is chosen if a     *)
(* quorum of acceptors have voted for it in the same ballot.               *)
(***************************************************************************)


(***************************************************************************)
(* The algorithm's variables.                                              *)
(***************************************************************************)
VARIABLE votes,   \* votes[a] is the set of votes cast by acceptor a
         maxBal   \* maxBal[a] is a ballot number.  Acceptor a will cast
                  \*   further votes only in ballots numbered \geq maxBal[a]

(***************************************************************************)
(* The type-correctness invariant.                                         *)
(***************************************************************************)
TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now make a series of definitions an assert some simple theorems      *)
(* about those definitions that lead to the algorithm.                     *)
(***************************************************************************)
VotedFor(a, b, v) == <<b, v>> \in votes[a]
  (*************************************************************************)
  (* True iff acceptor a has voted for v in ballot b.                      *)
  (*************************************************************************)
  
ChosenAt(b, v) == \E Q \in Quorum : 
                     \A a \in Q : VotedFor(a, b, v)
  (*************************************************************************)
  (* True iff a quorum of acceptors have all voted for v in ballot b.      *)
  (*************************************************************************)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}
  (*************************************************************************)
  (* The set of values that have been chosen.                              *)
  (*************************************************************************)
  
DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v) 

CannotVoteAt(a, b) == /\ maxBal[a] > b
                      /\ DidNotVoteAt(a, b)
  (*************************************************************************)
  (* Because acceptor a will not cast any more votes in a ballot numbered  *)
  (* < maxBal[a], this implies that a has not and will never cast a vote   *)
  (* in ballot b.                                                          *)
  (*************************************************************************)

NoneOtherChoosableAt(b, v) == 
   \E Q \in Quorum :
     \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)
  (*************************************************************************)
  (* If this is true, then ChosenAt(b, w) is not and can never become true *)
  (* for any w # v.                                                        *)
  (*************************************************************************)

SafeAt(b, v) == \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)
  (*************************************************************************)
  (* If this is true, then no value other than v has been or can ever be   *)
  (* chosen in any ballot numbered less than b.                            *)
  (*************************************************************************)
-----------------------------------------------------------------------------
THEOREM AllSafeAtZero == \A v \in Value : SafeAt(0, v)
-----------------------------------------------------------------------------
THEOREM ChoosableThm ==
          \A b \in Ballot, v \in Value : 
             ChosenAt(b, v) => NoneOtherChoosableAt(b, v)
-----------------------------------------------------------------------------
VotesSafe == \A a \in Acceptor, b \in Ballot, v \in Value :
                 VotedFor(a, b, v) => SafeAt(b, v)

OneVote == \A a \in Acceptor, b \in Ballot, v, w \in Value : 
              VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)
OneValuePerBallot ==  
    \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : 
       VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)
-----------------------------------------------------------------------------
THEOREM OneValuePerBallot => OneVote
-----------------------------------------------------------------------------
THEOREM VotesSafeImpliesConsistency ==
          /\ TypeOK 
          /\ VotesSafe
          /\ OneVote
          => \/ chosen = {}
             \/ \E v \in Value : chosen = {v}
-----------------------------------------------------------------------------
ShowsSafeAt(Q, b, v) == 
  /\ \A a \in Q : maxBal[a] \geq b
  /\ \E c \in -1..(b-1) : 
      /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
      /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)
-----------------------------------------------------------------------------
THEOREM ShowsSafety == 
          TypeOK /\ VotesSafe /\ OneValuePerBallot =>
             \A Q \in Quorum, b \in Ballot, v \in Value :
               ShowsSafeAt(Q, b, v) => SafeAt(b, v)
 
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now write the specification.  The initial condition is               *)
(* straightforward.                                                        *)
(***************************************************************************)
Init == /\ votes = [a \in Acceptor |-> {}]
        /\ maxBal = [a \in Acceptor |-> -1]


(***************************************************************************)
(* Next are the actions that make up the next-state action.                *)
(*                                                                         *)
(* An acceptor a is allowed to increase maxBal[a] to a ballot number b at  *)
(* any time.                                                               *)
(***************************************************************************)
IncreaseMaxBal(a, b) ==
  /\ b > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = b]
  /\ UNCHANGED votes

(***************************************************************************)
(* Next is the action in which acceptor a votes for v in ballot b.  The    *)
(* first four conjuncts re enabling conditions.  The first maintains the   *)
(* requirement that the acceptor cannot cast a vote in a ballot less than  *)
(* maxBal[a].  The next two conjuncts maintain the invariance of           *)
(* OneValuePerBallot.  The fourth conjunct maintains the invariance of     *)
(* VotesSafe.                                                              *)
(***************************************************************************)
VoteFor(a, b, v) ==
    /\ maxBal[a] \leq b
    /\ \A vt \in votes[a] : vt[1] # b
    /\ \A c \in Acceptor \ {a} : 
         \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]


(***************************************************************************)
(* The next-state action and the invariant.                                *)
(***************************************************************************)
Next  ==  \E a \in Acceptor, b \in Ballot : 
            \/ IncreaseMaxBal(a, b)
            \/ \E v \in Value : VoteFor(a, b, v)

Spec == Init /\ [][Next]_<<votes, maxBal>>

Inv == TypeOK /\ VotesSafe /\ OneValuePerBallot
-----------------------------------------------------------------------------
THEOREM Invariance == Spec => []Inv
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following statement instantiates module Consensus with the constant *)
(* Value of this module substituted for the constant Value of module       *)
(* Consensus, and the state function `chosen' defined in this module       *)
(* substituted for the variable `chosen' of module Value.  More precisely, *)
(* for each defined identifier id of module Value, this statement defines  *)
(* C!id to equal the value of id under these substitutions.                *)
(***************************************************************************)
C == INSTANCE Consensus

THEOREM Spec => C!Spec 
<1>1. Inv /\ Init => C!Init
<1>2. Inv /\ [Next]_<<votes, maxBal>> => [C!Next]_chosen
<1>3. QED
  <2>1. []Inv /\ [][Next]_<<votes, maxBal>> => [][C!Next]_chosen
    BY <1>2 \* and temporal reasoning
  <2>2. []Inv /\ Spec => C!Spec
    BY <2>1, <1>1
  <2>3. QED
    BY <2>2, Invariance
=============================================================================

