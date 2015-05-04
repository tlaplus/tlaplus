----------------------------- MODULE VoteProof ------------------------------ 

(*************************************************************************)
(*                     !!!! REGRESSION TESTS ONLY !!!!                   *)
(*                                                                       *)
(* This file is not meant as a reference to TLA+ in general, nor for     *)
(* VoteProof in particular. Please search the web for an official        *)
(* version of the VoteProof spec.                                        *)
(*                                                                       *)
(*************************************************************************)

EXTENDS Integers , FiniteSets, TLC, TLAPS 

CONSTANT Value,     \* As in module Consensus, the set of choosable values.
         Acceptor,  \* The set of all acceptors.
         Quorum     \* The set of all quorums.

ASSUME QA == /\ \A Q \in Quorum : Q \subseteq Acceptor
             /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}  
 
THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
PROOF BY QA

Ballot == Nat
 
(***************************
--algorithm Voting {
  variables votes = [a \in Acceptor |-> {}],
            maxBal = [a \in Acceptor |-> -1];
  define {
   VotedFor(a, b, v) == <<b, v>> \in votes[a]
   DidNotVoteIn(a, b) == \A v \in Value : ~ VotedFor(a, b, v) 

   SafeAt(b, v) ==
     LET SA[bb \in Ballot] ==
           \/ bb = 0
           \/ \E Q \in Quorum :
                /\ \A a \in Q : maxBal[a] \geq bb
                /\ \E c \in -1..(bb-1) :
                     /\ (c # -1) => /\ SA[c]
                                    /\ \A a \in Q :
                                         \A w \in Value :
                                            VotedFor(a, c, w) => (w = v)
                     /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
     IN  SA[b]
    }
  macro IncreaseMaxBal(b) {
    when b > maxBal[self] ;
    maxBal[self] := b
    }
    
  macro VoteFor(b, v) {
    when /\ maxBal[self] \leq b
         /\ DidNotVoteIn(self, b)
         /\ \A p \in Acceptor \ {self} : 
               \A w \in Value : VotedFor(p, b, w) => (w = v)
         /\ SafeAt(b, v) ;
    votes[self]  := votes[self] \cup {<<b, v>>};
    maxBal[self] := b 
    }
    
  process (acceptor \in Acceptor) {
    acc : while (TRUE) {
           with (b \in Ballot) {
             either IncreaseMaxBal(b)
             or     with (v \in Value) { VoteFor(b, v) }
       }
     }
    }
}

The following is the TLA+ specification produced by the translation.
Blank lines, produced by the translation because of the comments, have
been deleted.
****************************)
\* BEGIN TRANSLATION
VARIABLES votes, maxBal

(* define statement *)
VotedFor(a, b, v) == <<b, v>> \in votes[a]



DidNotVoteIn(a, b) == \A v \in Value : ~ VotedFor(a, b, v)





















SafeAt(b, v) ==
  LET SA[bb \in Ballot] ==



        \/ bb = 0
        \/ \E Q \in Quorum :
             /\ \A a \in Q : maxBal[a] \geq bb
             /\ \E c \in -1..(bb-1) :
                  /\ (c # -1) => /\ SA[c]
                                 /\ \A a \in Q :
                                      \A w \in Value :
                                         VotedFor(a, c, w) => (w = v)
                  /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
  IN  SA[b]


vars == << votes, maxBal >>

ProcSet == (Acceptor)

Init == (* Global variables *)
        /\ votes = [a \in Acceptor |-> {}]
        /\ maxBal = [a \in Acceptor |-> -1]

acceptor(self) == \E b \in Ballot:
                    \/ /\ b > maxBal[self]
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ votes' = votes
                    \/ /\ \E v \in Value:
                            /\ /\ maxBal[self] \leq b
                               /\ DidNotVoteIn(self, b)
                               /\ \A p \in Acceptor \ {self} :
                                     \A w \in Value : VotedFor(p, b, w) => (w = v)
                               /\ SafeAt(b, v)
                            /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
                            /\ maxBal' = [maxBal EXCEPT ![self] = b]

Next == (\E self \in Acceptor: acceptor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

THEOREM RecursiveFcnOfNat ==
          ASSUME NEW Def(_,_), 
                 \A n \in Nat : 
                    \A g, h : (\A i \in 0..(n-1) : g[i] = h[i]) => (Def(g, n) = Def(h, n))
          PROVE  LET f[n \in Nat] == Def(f, n)
                 IN  f = [n \in Nat |-> Def(f, n)]
PROOF OMITTED

THEOREM SafeAtProp ==
  \A b \in Ballot, v \in Value :
    SafeAt(b, v) =
      \/ b = 0
      \/ \E Q \in Quorum :
           /\ \A a \in Q : maxBal[a] \geq b
           /\ \E c \in -1..(b-1) :
                /\ (c # -1) => /\ SafeAt(c, v)
                               /\ \A a \in Q :
                                    \A w \in Value :
                                        VotedFor(a, c, w) => (w = v)
                /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
<1>1. SUFFICES ASSUME NEW v \in Value
               PROVE  \A b \in Ballot : SafeAtProp!(b, v)
  OBVIOUS
<1> USE DEF Ballot
<1> DEFINE Def(SA, bb) ==
        \/ bb = 0
        \/ \E Q \in Quorum :
             /\ \A a \in Q : maxBal[a] \geq bb
             /\ \E c \in -1..(bb-1) :
                  /\ (c # -1) => /\ SA[c]
                                 /\ \A a \in Q :
                                      \A w \in Value :
                                         VotedFor(a, c, w) => (w = v)
                  /\ \A d \in (c+1)..(bb-1), a \in Q : DidNotVoteIn(a, d)
      SA[bb \in Ballot] == Def(SA, bb)
<1>2. \A b : SafeAt(b, v) = SA[b]
  BY DEF SafeAt
<1>3. \A n \in Nat : 
         \A g, h : (\A i \in 0..(n-1) : g[i] = h[i]) => (Def(g, n) = Def(h, n))
  BY SMT
<1> HIDE DEF Def
<1>4. SA = [b \in Ballot |-> Def(SA, b)]
  BY ONLY <1>3, RecursiveFcnOfNat    
<1>5. \A b \in Ballot : SA[b] = Def(SA, b)
  BY <1>4
<1>6. QED
  BY <1>2, <1>5 DEF SafeAt, Def

TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

ChosenIn(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenIn(b, v)}

AXIOM SimpleNatInduction == \A f : /\ f[0]
                                   /\ \A n \in Nat : f[n] => f[n+1]
                                   => \A n \in Nat : f[n]

THEOREM GeneralNatInduction == 
         \A f : /\ f[0]
                /\ \A n \in Nat : (\A j \in 0..n : f[j]) => f[n+1]
                => \A n \in Nat : f[n]
<1>1. SUFFICES ASSUME NEW f,
                      f[0],
                      \A m \in Nat : (\A j \in 0..m : f[j]) => f[m+1],
                      NEW n \in Nat
               PROVE  f[n]
  OBVIOUS
<1> DEFINE g == [m \in Nat |-> \A j \in 0..m : f[j]]
<1>2. g[0]
  BY <1>1, SMT
<1>3. ASSUME NEW k \in Nat,  g[k]
      PROVE  g[k+1]
  BY <1>1, <1>3, SMT
<1>4. \A k \in Nat : g[k]
  BY <1>2, <1>3, SimpleNatInduction
<1>5. QED  
  BY <1>4, SMT                         

LEMMA SafeLemma == 
       TypeOK => 
         \A b \in Ballot :
           \A v \in Value :
              SafeAt(b, v) => 
                \A c \in 0..(b-1) :
                  \E Q \in Quorum :
                    \A a \in Q : /\ maxBal[a] >= c
                                 /\ \/ DidNotVoteIn(a, c)
                                    \/ VotedFor(a, c, v)
<1> SUFFICES ASSUME TypeOK
             PROVE  SafeLemma!2
  OBVIOUS
<1> DEFINE P[b \in Ballot] == \A c \in 0..b : SafeLemma!2!(c)
<1>1. P[0]
  BY SMT DEF Ballot  
<1>2. ASSUME NEW b \in Ballot, P[b]
      PROVE  P[b+1]
  <2>1. /\ b+1 \in Ballot 
        /\ (b+1) - 1 = b
    BY SMT DEF Ballot
  <2>2. 0..(b+1) = (0..b) \cup {b+1}
    BY SMT DEF Ballot
  <2>3. SUFFICES ASSUME NEW v \in Value,
                        SafeAt(b+1, v),
                        NEW c \in 0..b
                 PROVE  \E Q \in Quorum :
                           \A a \in Q : /\ maxBal[a] >= c
                                        /\ \/ DidNotVoteIn(a, c)
                                           \/ VotedFor(a, c, v)
    BY <1>2, <2>1, <2>2  
  <2>4. PICK Q \in Quorum : 
               /\ \A a \in Q : maxBal[a] \geq (b+1)
               /\ \E cc \in -1..b :
                    /\ (cc # -1) => /\ SafeAt(cc, v)
                                    /\ \A a \in Q :
                                         \A w \in Value :
                                            VotedFor(a, cc, w) => (w = v)
                    /\ \A d \in (cc+1)..b, a \in Q : DidNotVoteIn(a, d)
    <3>1. b+1 # 0
      BY SMT DEF Ballot
    <3>2. SafeAt(b+1,v) = SafeAtProp!(b+1,v)!2
       BY SafeAtProp, <2>1
    <3>3. @ = SafeAtProp!(b+1,v)!2!2
      BY <3>1
    <3>4. @ = \E Q \in Quorum : 
               /\ \A a \in Q : maxBal[a] \geq (b+1)
               /\ \E cc \in -1..b :
                    /\ (cc # -1) => /\ SafeAt(cc, v)
                                    /\ \A a \in Q :
                                         \A w \in Value :
                                            VotedFor(a, cc, w) => (w = v)
                    /\ \A d \in (cc+1)..b, a \in Q : DidNotVoteIn(a, d)
      BY <2>1
    <3>5. QED
      BY <3>2, <3>3, <3>4, <2>3 
  <2>5. PICK cc \in -1..b : 
               /\ (cc # -1) => /\ SafeAt(cc, v)
                               /\ \A a \in Q :
                                     \A w \in Value :
                                        VotedFor(a, cc, w) => (w = v)
               /\ \A d \in (cc+1)..b, a \in Q : DidNotVoteIn(a, d)
    BY <2>4
  <2>6. CASE c > cc
    BY <2>6, <2>5, <2>4, QA, SMT DEF TypeOK, Ballot
  <2>7. CASE c =< cc
    <3>1. /\ cc \in 0..b
          /\ cc # -1
      BY <2>7, SMT DEF Ballot
    <3>2. SafeLemma!2!(cc)!(v)
      BY <1>2, <3>1
    <3>3. SafeAt(cc, v)
      BY <2>5, <3>1
    <3>4. CASE c = cc
      BY <3>4, <3>1, <2>5, <2>4, SMT DEF Ballot, TypeOK, DidNotVoteIn
    <3>5. CASE c < cc
      <4>1. c \in 0..(cc-1)
        BY <3>1, <3>5, SMT
      <4>2. SafeLemma!2!(cc)
        BY <3>1, <1>2
      <4>3. QED
        BY <4>1,<4>2, <4>2, <3>3
    <3>6. QED
      BY <2>7, <3>4, <3>5, SMT DEF Ballot
  <2>8. QED
    BY <2>6, <2>7, SMT DEF Ballot
<1>3. \A b \in Ballot : P[b]
  BY <1>1, <1>2, SimpleNatInduction DEF Ballot
<1>4. QED
  BY <1>3, Z3 DEF Ballot \* SMT fails

VInv1 == \A a \in Acceptor, b \in Ballot, v, w \in Value : 
           VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)

VInv2 == \A a \in Acceptor, b \in Ballot, v \in Value :
                  VotedFor(a, b, v) => SafeAt(b, v)

VInv3 ==  \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : 
                VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

THEOREM VInv3 => VInv1
BY DEF VInv1, VInv3

LEMMA VT0 == /\ TypeOK
             /\ VInv1
             /\ VInv2
             => \A v, w \in Value, b, c \in Ballot : 
                   (b > c) /\ SafeAt(b, v) /\ ChosenIn(c, w) => (v = w)
<1> SUFFICES ASSUME TypeOK, VInv1, VInv2,
                    NEW v \in Value, NEW w \in Value 
             PROVE  \A b, c \in Ballot : 
                      (b > c) /\ SafeAt(b, v) /\ ChosenIn(c, w) => (v = w)
  OBVIOUS
<1> P == [b \in Ballot |-> 
            \A c \in Ballot : 
            (b > c) /\ SafeAt(b, v) /\ ChosenIn(c, w) => (v = w)]

<1>1. P[0]
  BY SMT DEF Ballot (* This works *)
<1>2. ASSUME NEW b \in Ballot, \A i \in 0..b : P[i]
      PROVE  P[b+1]
  <2>1. b+1 \in Ballot
    BY SMT DEF Ballot
  <2>2. SUFFICES ASSUME NEW c \in Ballot, b+1 > c, SafeAt(b+1, v), ChosenIn(c, w)
                 PROVE  v=w
    BY <2>1
  <2>3. PICK Q \in Quorum : \A a \in Q : VotedFor(a, c, w)
    BY <2>2 DEF ChosenIn
  <2>4. b+1 # 0 /\ ((b+1)-1 = b) 
    BY SMT DEF Ballot
  <2>5. PICK QQ \in Quorum, 
              d \in -1..((b+1)-1) :
                /\ (d # -1) => /\ SafeAt(d, v)
                               /\ \A a \in QQ :
                                    \A x \in Value :
                                        VotedFor(a, d, x) => (x = v)
                /\ \A e \in (d+1)..((b+1)-1), a \in QQ : DidNotVoteIn(a, e)
   BY <2>1, <2>2, <2>4, SafeAtProp
  <2> PICK aa \in QQ \cap Q : TRUE
    BY QA
  <2>6. c \leq d 
    BY <2>2, <2>3, <2>5, SMT DEF DidNotVoteIn, Ballot 
  <2>7. d # -1
    BY <2>6, SMT DEF Ballot
  <2>8. CASE c = d
    BY <2>3, <2>5, <2>7, <2>8
  <2>9. CASE d > c
    <3>1. SafeAt(d, v)
      BY <2>5, <2>7
    <3>2. d \in Ballot /\ d \in 0..b 
      BY <2>6, SMT DEF Ballot
    <3>3. P[d]
      BY <1>2, <3>2
    <3>4. QED
      BY <2>2, <2>9, <3>1,  <3>2, <3>3
  <2>10. QED
    BY <2>3, <2>6, <2>8, <2>9, SMT DEF Ballot 
<1>3. \A b \in Ballot : P[b]
  BY <1>1, <1>2, GeneralNatInduction DEF Ballot

<1>4. QED
  BY <1>3
 
THEOREM VT1 == /\ TypeOK 
               /\ VInv1
               /\ VInv2
               => \A v, w : 
                    (v \in chosen) /\ (w \in chosen) => (v = w)
<1>1. SUFFICES ASSUME TypeOK, VInv1, VInv2,
                      NEW v, NEW w, 
                      v \in chosen, w \in chosen
               PROVE  v = w
  OBVIOUS
<1>2. v \in Value /\ w \in Value
  BY <1>1 DEF chosen
<1>3. PICK b \in Ballot, c \in Ballot : ChosenIn(b, v) /\ ChosenIn(c, w)
  BY <1>1 DEF chosen
<1>4. PICK Q \in Quorum, R \in Quorum : 
         /\ \A a \in Q : VotedFor(a, b, v)
         /\ \A a \in R : VotedFor(a, c, w)
  BY <1>3 DEF ChosenIn
<1>5. PICK av \in Q, aw \in R: /\ VotedFor(av, b, v)
                               /\ VotedFor(aw, c, w)
  BY <1>4, QuorumNonEmpty
<1>6. SafeAt(b, v) /\ SafeAt(c, w)
  BY <1>1, <1>2, <1>5, QA DEF VInv2
<1>7. CASE b = c
  <2> PICK a \in Q \cap R : TRUE
    BY QA
  <2>1. /\ VotedFor(a, b, v)
        /\ VotedFor(a, c, w)
    BY <1>4
  <2>2. QED
    BY <1>1, <1>2, <1>7, <2>1, QA DEF VInv1
<1>8. CASE b > c
  BY <1>1, <1>6, <1>3, <1>8, VT0, <1>2 \* <2>1
<1>9. CASE c > b
    BY <1>1, <1>6, <1>3, <1>9, VT0, <1>2 \* <2>1
<1>10. QED
  BY <1>7, <1>8, <1>9 DEF Ballot

VInv4 == \A a \in Acceptor, b \in Ballot : 
            maxBal[a] < b => DidNotVoteIn(a, b)
             
VInv == TypeOK /\ VInv2 /\ VInv3 /\ VInv4

IncreaseMaxBal(self, b) ==  
  /\ b > maxBal[self]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ UNCHANGED votes

VoteFor(self, b, v) == 
  /\ maxBal[self] \leq b
  /\ DidNotVoteIn(self, b)
  /\ \A p \in Acceptor \ {self} :
        \A w \in Value : VotedFor(p, b, w) => (w = v)
  /\ SafeAt(b, v)
  /\ votes' = [votes EXCEPT ![self] = votes[self] \cup {<<b, v>>}]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]

BallotAction(self, b) ==
  \/ IncreaseMaxBal(self, b)
  \/ \E v \in Value : VoteFor(self, b, v)

ASSUME AcceptorNonempty == Acceptor # {}

LEMMA NextDef ==
  TypeOK => 
   (Next =  \E self \in Acceptor :
                 \E b \in Ballot : BallotAction(self, b) )
<1> HAVE TypeOK
<1>2. Next = \E self \in Acceptor: acceptor(self)
 BY AcceptorNonempty DEF Next, ProcSet
<1>3. @ = NextDef!2!2
  BY DEF Next, BallotAction, IncreaseMaxBal, VoteFor, ProcSet, acceptor
<1>4. QED  
  BY <1>2, <1>3

THEOREM InductiveInvariance == VInv /\ [Next]_vars => VInv'
<1>1. VInv /\ (vars' = vars) => VInv'
  \* SMT can't do this because it requires the definition of SafeAt,
  \* which uses a recursive function definition.
  <2> SUFFICES ASSUME VInv, vars' = vars
               PROVE  VInv'
    OBVIOUS
  <2> USE DEF vars, VInv
  <2>1. TypeOK'
    BY DEF TypeOK
  <2>2. VInv2'
    BY DEF VInv2, VotedFor, SafeAt, DidNotVoteIn
  <2>3. VInv3'
    BY DEF VInv3, VotedFor
  <2>4. VInv4'
    BY DEF VInv4, DidNotVoteIn, VotedFor
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4 

<1> SUFFICES ASSUME VInv, 
                    NEW self \in Acceptor,
                    NEW b \in Ballot, 
                    BallotAction(self, b)
             PROVE  VInv'
  BY <1>1, NextDef DEF VInv

<1>2. TypeOK'
  <2>1. CASE IncreaseMaxBal(self, b)
    BY <2>1 DEF IncreaseMaxBal, VInv, TypeOK
  <2>2. CASE \E v \in Value : VoteFor(self, b, v)
    BY <2>2 DEF VInv, TypeOK, VoteFor  \* SMT and Zenon failed
  <2>3. QED
    BY <2>1, <2>2 DEF BallotAction

<1>3. ASSUME NEW a \in Acceptor, NEW c \in Ballot, NEW w \in Value,
             ~VotedFor(a, c, w), VotedFor(a, c, w)'
      PROVE  (a = self) /\ (c = b) /\ VoteFor(self, b, w) 
  BY <1>3, SMT DEF IncreaseMaxBal, VInv, TypeOK, VotedFor, VoteFor, BallotAction
    
<1>4. ASSUME NEW a \in Acceptor
      PROVE  /\ maxBal[a] \in Ballot \cup {-1}
             /\ maxBal'[a] \in Ballot \cup {-1}
             /\ maxBal'[a] >= maxBal[a]
  BY SMT DEF VInv, TypeOK, IncreaseMaxBal, VInv, VoteFor, BallotAction, 
             DidNotVoteIn, VotedFor, Ballot  
    
<1>5. ASSUME NEW c \in Ballot, NEW w \in Value,
             SafeAt(c, w)
      PROVE  SafeAt(c, w)'
  <2>SafeAtPropPrime. SafeAtProp'
    BY SafeAtProp, PTL
  <2> DEFINE P[i \in Ballot] == \A j \in 0..i : SafeAt(j, w) => SafeAt(j, w)'
  <2>1. P[0]
    <3>1. 0 \in Ballot /\ \A i \in 0..0 : i = 0
      BY SMT DEF Ballot
    <3>2. QED
      BY <2>SafeAtPropPrime, <3>1
  <2>2. ASSUME NEW d \in Ballot, P[d]
        PROVE  P[d+1]
    <3>1. d+1 \in Ballot /\ d+1 # 0
      BY SMT DEF Ballot
    <3>2. SUFFICES ASSUME NEW e \in 0..(d+1), SafeAt(e, w)
                   PROVE  SafeAt(e, w)'
      BY <3>1
    <3>3. e \in 0..d \/ e = d+1
      BY SMT DEF Ballot
    <3>4. CASE e \in 0..d
      BY <2>2, <3>2, <3>4
    <3>5. CASE e = d+1      
      <4>1. PICK Q \in Quorum : SafeAtProp!(e, w)!2!2!(Q)
        BY <3>1, <3>2, <3>5, SafeAtProp
      <4>2. \A aa \in Q : maxBal'[aa] \geq e
        BY <1>4, <4>1, QA, SMT DEF Ballot
      <4>3. \E cc \in -1..(e-1) : 
               /\ (cc # -1) => /\ SafeAt(cc, w)'
                               /\ \A ax \in Q :
                                    \A z \in Value :
                                        VotedFor(ax, cc, z)' => (z = w)
               /\ \A dd \in (cc+1)..(e-1), ax \in Q : DidNotVoteIn(ax, dd)'
        <5>1. PICK cc \in -1..(e-1) : 
               /\ (cc # -1) => /\ SafeAt(cc, w)
                               /\ \A ax \in Q :
                                    \A z \in Value :
                                        VotedFor(ax, cc, z) => (z = w)
               /\ \A dd \in (cc+1)..(e-1), ax \in Q : DidNotVoteIn(ax, dd)
          BY <1>5, <3>3, <2>2, <4>1
        <5>2. (cc # -1) => (SafeAt(cc, w) => SafeAt(cc, w)')
            BY <2>2  DEF Ballot
        <5>3. CASE IncreaseMaxBal(self, b)
          <6>1. /\ \A x, y, z : VotedFor(x, y, z)' = VotedFor(x,y,z)
                /\ \A x, y: DidNotVoteIn(x, y)' = DidNotVoteIn(x, y)
             BY <5>3 DEF IncreaseMaxBal, VotedFor, DidNotVoteIn
          <6>2 QED
            BY <5>1, <5>2, <6>1
        <5>4. CASE \E v \in Value : VoteFor(self, b, v)
          <6> PICK v \in Value : VoteFor(self, b, v)
            BY <5>4
          <6> QED
            BY <5>4, <4>2, <5>1, <5>2, <2>2, QA 
            DEF VoteFor, VotedFor, DidNotVoteIn, VInv, TypeOK, Ballot
        <5>5. QED
          BY <5>3, <5>4 DEF BallotAction
      <4>4.  \/ e = 0
             \/ \E Q_1 \in Quorum :
                   /\ \A aa \in Q_1 : maxBal'[aa] \geq e
                   /\ \E c_1 \in -1..e - 1 :
                         /\ c_1 # -1
                            => (/\ SafeAt(c_1, w)'
                                /\ \A aa \in Q_1 :
                                      \A w_1 \in Value :
                                         VotedFor(aa, c_1, w_1)' => w_1 = w)
                         /\ \A d_1 \in c_1 + 1..e - 1, aa \in Q_1 :
                               DidNotVoteIn(aa, d_1)'
         BY <4>2, <4>3, <3>1, <3>5
      <4>5. e \in Ballot
        BY <3>1, <3>5
      <4>6. SafeAt(e, w)' = <4>4
        BY <2>SafeAtPropPrime, <4>5
      <4>7. QED
        BY <4>2, <4>3, <4>6 
    <3>6. QED
      BY <3>3, <3>4, <3>5
  <2>3. \A d \in Ballot : P[d]
    BY <2>1, <2>2, SimpleNatInduction DEF Ballot
  <2>4. QED
    BY <2>3, <1>5, SMT DEF Ballot

<1>6. VInv2'
  BY <1>3, <1>5, SMT DEF VInv, VInv2, VoteFor

<1>7. VInv3'
  BY <1>3, SMT DEF VoteFor, DidNotVoteIn, VInv, TypeOK, VotedFor, VInv, VInv3

<1>8. VInv4'
  BY <1>3, <1>4, SMT DEF Ballot, VInv, VInv4, VoteFor, DidNotVoteIn, TypeOK

<1>9. QED
  BY <1>2, <1>6, <1>7, <1>8 DEF VInv

THEOREM InitImpliesInv == Init => VInv
<1> SUFFICES ASSUME Init PROVE VInv
  OBVIOUS
<1> USE DEF Init
<1>1. TypeOK
  BY DEF TypeOK, ProcSet
<1>2. VInv2
  BY  DEF VInv2, VotedFor
<1>3. VInv3
  BY DEF VInv3, VotedFor
<1>4. VInv4
  BY DEF VInv4, DidNotVoteIn, VotedFor
<1>5. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF VInv

THEOREM VT2 == Spec => []VInv
  BY InductiveInvariance, InitImpliesInv, PTL DEF Spec

C == INSTANCE Consensus 

THEOREM VT3 == Spec => C!Spec 
<1>1. Init => C!Init
  BY QuorumNonEmpty, QA, SMT DEF Init, C!Init, chosen, ChosenIn, VotedFor

<1>2. ASSUME VInv, VInv', [Next]_vars
      PROVE  [C!Next]_C!vars
  <2> USE VInv
  <2>1. CASE vars' = vars
    BY <2>1 DEF vars, C!vars, chosen, ChosenIn, VotedFor
  <2>2. SUFFICES ASSUME NEW self \in Acceptor,
                        NEW b \in Ballot, 
                        BallotAction(self, b)
                 PROVE  [C!Next]_C!vars
    BY <1>2, <2>1, NextDef DEF VInv 
  <2>3. ASSUME IncreaseMaxBal(self, b)
        PROVE  C!vars' = C!vars
    BY <2>3 DEF IncreaseMaxBal, C!vars, chosen, ChosenIn, VotedFor
  <2>4. ASSUME NEW v \in Value,
               VoteFor(self, b, v)
        PROVE  [C!Next]_C!vars
    <3>3. ASSUME NEW w \in chosen
          PROVE  w \in chosen'
      BY <3>3, <2>4, <1>2, QA, SMT 
      DEF VoteFor, VInv, TypeOK, chosen, ChosenIn, VotedFor
    <3>VT1P. VT1'
      BY VT1, PTL
    <3>1. ASSUME NEW w \in chosen,
                     v \in chosen'
          PROVE  w = v
      BY <1>2, <3>1, <3>3, <3>VT1P, SMT DEF VInv, VInv1, VInv3 
    <3>2. ASSUME NEW w, w \notin chosen, w \in chosen'
          PROVE  w = v
      BY <3>2, <2>4, <1>2, QA, SMT
      DEF chosen, ChosenIn, VotedFor, VoteFor, VInv, TypeOK
    <3>4. CASE chosen' = chosen
      BY <3>4 DEF C!vars
    <3>5. CASE chosen' # chosen
      <4>1. chosen \subseteq chosen'
        BY <3>3
      <4>2. PICK w \in chosen' : w \notin chosen
        BY <3>5, <4>1
      <4>3. w = v
        BY <4>2, <3>2
      <4>4. chosen' = chosen \cup {v}
        BY <3>2, <4>1, <4>3
      <4>5. chosen = {}
        BY <4>4, <3>1, <3>5
      <4>6. QED
        BY <4>4, <4>5 DEF C!Next
    <3>6. QED
      BY <3>4, <3>5
  <2>5. QED
    BY <2>2, <2>3, <2>4 DEF BallotAction
    
<1>3. QED
  BY <1>1, <1>2, VT2, PTL DEF C!Spec, Spec

ASSUME AcceptorFinite == IsFiniteSet(Acceptor)

ASSUME ValueNonempty == Value # {}

AXIOM SubsetOfFiniteSetFinite == 
        \A S, T : IsFiniteSet(T) /\ (S \subseteq T) => IsFiniteSet(S)

AXIOM FiniteSetHasMax == 
        \A S \in SUBSET Int :
          IsFiniteSet(S) /\ (S # {}) => \E max \in S : \A x \in S : max >= x

AXIOM IntervalFinite == \A i, j \in Int : IsFiniteSet(i..j)

THEOREM VT4 == TypeOK /\ VInv2 /\ VInv3  =>
                \A Q \in Quorum, b \in Ballot :
                   (\A a \in Q : (maxBal[a] >= b)) => \E v \in Value : SafeAt(b,v)

<1>1. SUFFICES ASSUME TypeOK, VInv2, VInv3,
                      NEW Q \in Quorum, NEW b \in Ballot,
                      (\A a \in Q : (maxBal[a] >= b))
               PROVE  \E v \in Value : SafeAt(b, v)
  OBVIOUS
<1>2. CASE b = 0
  BY ValueNonempty, <1>1, SafeAtProp, <1>2
<1>3. SUFFICES ASSUME b # 0
               PROVE  \E v \in Value : SafeAt(b, v)
  BY <1>2
<1>4. SUFFICES \E v \in Value : 
                 \E c \in -1..(b-1) :
                   /\ (c # -1) => /\ SafeAt(c, v)
                                  /\ \A a \in Q :
                                       \A w \in Value :
                                           VotedFor(a, c, w) => (w = v)
                   /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
  <2>1. SUFFICES ASSUME NEW v \in Value,
                        <1>4!1!(v)
                 PROVE  SafeAt(b, v)
    OBVIOUS
  <2>2. SafeAtProp!(b, v)
    BY SafeAtProp
  <2>3. QED
    BY <2>1, <2>2, <1>1, <1>3
<1>5. CASE \A a \in Q, c \in 0..(b-1) : DidNotVoteIn(a, c)
  <2>1. PICK v \in Value : TRUE
    BY ValueNonempty
  <2> -1 \in -1..(b-1)
    BY SMT DEF Ballot
  <2>2. WITNESS v \in Value
  <2>3. WITNESS -1 \in -1..(b-1)
  <2>4. QED
    BY <1>5
<1>6. CASE \E a \in Q, c \in 0..(b-1) : ~DidNotVoteIn(a, c)
  <2>1. PICK c \in 0..(b-1) : 
               /\ \E a \in Q : ~DidNotVoteIn(a, c)
               /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
    <3> DEFINE S == {c \in 0..(b-1) : \E a \in Q : ~DidNotVoteIn(a, c)}
    <3>1. S # {}
        BY <1>6
    <3>2. PICK c \in S : \A d \in S : c >= d
      <4>1. (0 \in Int) /\ (b-1 \in Int)  /\ (\A x \in 0..(b-1) : x \in Int)
        BY <1>3, SMT DEF Ballot
      <4>2. (S \in SUBSET Int) 
        BY <4>1
      <4>3. IsFiniteSet(S)
        BY <4>1, IntervalFinite, SubsetOfFiniteSetFinite
      <4>4. QED
        BY <3>1,  <4>2, <4>3, FiniteSetHasMax
    <3>3. c \in 0..(b-1)
      OBVIOUS
    <3>4. \A d \in (c+1)..(b-1) : d \in 0..(b-1) /\ ~(c >= d)
      BY <3>3, SMT DEF Ballot  (* This works *)
    <3>5. \A d \in (c+1)..(b-1), a \in Q : DidNotVoteIn(a, d)
      BY <3>2, <3>4
    <3>6. \E a \in Q : ~DidNotVoteIn(a, c)
      BY <3>1
    <3>7. QED
      BY  <3>3, <3>5, <3>6
  <2>2. (c \in -1..(b-1)) /\ (c # -1) /\ (c \in Ballot)
    BY SMT DEF Ballot
  <2>3. PICK a0 \in Q : ~DidNotVoteIn(a0, c)
    BY <2>1
  <2>4. PICK v \in Value : VotedFor(a0, c, v)
    BY <2>3 DEF DidNotVoteIn
  <2>5. \A a \in Q : \A w \in Value :
           VotedFor(a, c, w) => (w = v)
    BY <2>2, <2>4, QA, <1>1 DEF VInv3
  <2>6. SafeAt(c, v)
    BY <1>1, <2>4, QA, <2>2 DEF VInv2
  <2>7. QED
    BY <2>1, <2>2, <2>5, <2>6 

<1>7. QED
  BY <1>5, <1>6

LiveAssumption ==
  \E Q \in Quorum, b \in Ballot :
     \A self \in Q :
       /\ WF_vars(BallotAction(self, b))
       /\ [] [\A c \in Ballot : (c > b) => ~ BallotAction(self, c)]_vars
      
LiveSpec == Spec /\ LiveAssumption  
===============================================================================
