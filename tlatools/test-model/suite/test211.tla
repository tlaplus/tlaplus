\* Test of moderately large proof.

`. last modified on Wed  4 March 2009 at 17:55:12 PST by lamport 
   Major changes made 21 Sep 2007:
     variable chosen renamed learned
     action Choose renamed Learn
   Major changes made 22 Sep 2007:
     removed variable noccmd
.'


--------------------------------- MODULE test211 --------------------------------
EXTENDS Integers, FiniteSets
-----------------------------------------------------------------------------
(***************************************************************************)
(*                                 CONSTANTS                               *)
(*                                                                         *)
(* For convenience, we take configuration numbers, instance numbers, and   *)
(* ballot numbers all to be the set of naturals.  However, to make the     *)
(* meanings of our formulas easier to understand, we use different names   *)
(* for these three equal sets.                                             *)
(***************************************************************************)
CNum == Nat  \* The set of configuration numbers.
INum == Nat  \* The set of instance numbers.
BNum == Nat  \* The set of ballot numbers.

CONSTANT Acc   \* The set of acceptors

(***************************************************************************)
(* We define Config to be the set of configurations, where a configuration *)
(* is a record with a cnum field that is the configuration number field    *)
(* and a quorums field that is a set of quorums, which is a set of         *)
(* pairwise non-disjoint sets of acceptors.                                *)
(***************************************************************************)
Config ==  [cnum    : CNum, 
            quorums : {C \in SUBSET SUBSET Acc : 
                         \A P1, P2 \in C : P1 \cap P2 # {}}]

CONSTANTS Cmd,           \* The set of commands (choosable values).

          ConfigCmd(_),  \* ConfigCmd(C) is the command that sets the 
                         \* current configuration to C.                    

          InitConfig     \* The initial configuration

(***************************************************************************)
(* We assume that ConfigCmd(C) is a distinct command for every             *)
(* configuration C, and that InitConfig is a configuration with cnum 0.    *)
(***************************************************************************)
ASSUME ConstantAssumption ==
  /\ \A C \in Config : ConfigCmd(C) \in  Cmd
  /\ \A C, D \in Config : (C # D) => (ConfigCmd(C) # ConfigCmd(D))    
  /\ InitConfig \in Config
  /\ InitConfig.cnum = 0

(***************************************************************************)
(* The configuration of a configuration command.                           *)
(***************************************************************************)
ConfigOfCmd(c) == CHOOSE C \in Config : c = ConfigCmd(C)


(***************************************************************************)
(* CCmd is the set of reconfiguration commands.                            *)
(***************************************************************************)
CCmd == {ConfigCmd(C) : C \in Config}

(***************************************************************************)
(* Vote is the set of votes, where a vote is a record with cnum            *)
(* (configuration number) field and cmd (command) field.  We define init   *)
(* and `none' to be two different values a that are not votes.             *)
(***************************************************************************)
Vote == [cnum : CNum, cmd : Cmd]
init == CHOOSE v : v \notin Vote 
none == CHOOSE v : v \notin Vote \cup {init}
-----------------------------------------------------------------------------
(***************************************************************************)
(*                                   VARIABLES                             *)
(*                                                                         *)
(* The algorithm has two variables avote and `learned', where:             *)
(*                                                                         *)
(* - avote[a][i][b] is either the vote cast by acceptor a in instance i    *)
(*   for ballot b.  It initially equals init from which it can be set to   *)
(*   a vote, to the value `none' indicating that `a' abstains in that      *)
(*   ballot.                                                               *)
(*                                                                         *)
(* - `learned' is the set of pairs <<i, cmd>> indicating that command cmd  *)
(*   has been learned in instance i.                                       *)
(***************************************************************************)
VARIABLE avote, learned

(***************************************************************************)
(* BOUND IDENTIFIER CONVENTIONS                                            *)
(*                                                                         *)
(* We use the following conventions for the names used in quantifiers and  *)
(* operator parameters:                                                    *)
(*                                                                         *)
(*   `a' : An acceptor                                                     *)
(*                                                                         *)
(*   i : An instance number.                                               *)
(*                                                                         *)
(*   b : A ballot number                                                   *)
(*                                                                         *)
(*   C : A configuration                                                   *)
(*                                                                         *)
(*   c, cmd : A command                                                    *)
(*                                                                         *)
(*   n, cnum : A configuration number.                                     *)
(*                                                                         *)
(* Multiple identifiers of the same type are named in an obvious way--for  *)
(* example b and bb, or c1 and c2.                                         *)
(***************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                           STATE PREDICATES                              *)
(*                                                                         *)
(* The initial predicate asserts that avote[a][i][b] = init for all `a',   *)
(* i, and b, and that `learned' contains the single element <<-1, c>>      *)
(* where c is the command that sets the current configuration to           *)
(* InitConfig.                                                             *)
(***************************************************************************)
Init == /\ avote  = [a \in Acc |-> [i \in INum |-> [b \in BNum |-> init]]]
        /\ learned = {<<-1, ConfigCmd(InitConfig)>>}

(***************************************************************************)
(* The following state predicate is true iff `a' voted in instance i at    *)
(* ballot b for command c with configuration number n.                     *)
(***************************************************************************)
Voted(a, i, b, n, c) == /\ avote[a][i][b] \in Vote
                        /\ avote[a][i][b] = [cnum |-> n, cmd |-> c]

(***************************************************************************)
(* A type correctness assertion, which is an invariant of the algorithm.   *)
(* It is trivial to check that this is true in the initial state and       *)
(* preserved by every step of the algorithm.                               *)
(***************************************************************************)
TypeOK == 
  /\ (**********************************************************************)
     (* avote is a function with the correct domain and range.             *)
     (**********************************************************************)
     avote \in [Acc -> [INum -> [BNum -> Vote \cup {init, none}] ] ]
     
  /\ (**********************************************************************)
     (* An acceptor votes only for a new configuration with a              *)
     (* configuration number 1 greater than that of the current            *)
     (* configuration.                                                     *)
     (**********************************************************************)
     \A a \in Acc, i \in INum, b \in BNum, n \in CNum, C \in Config :
        Voted(a, i, b, n, ConfigCmd(C)) => (C.cnum = n+1)

  /\ (**********************************************************************)
     (* `learned' is a set of elements of the proper type.                 *)
     (**********************************************************************)
     learned \subseteq (INum \cup {-1}) \X Cmd

  /\ (**********************************************************************)
     (* There is exactly one element of the form <<-1, c>> \in learned,    *)
     (* where c is the command that sets the configuration to InitConfig.  *)
     (**********************************************************************)
     \A c \in Cmd : (<<-1, c>> \in learned) <=> (c = ConfigCmd(InitConfig))     


(***************************************************************************)
(* The following state predicates are the usual ones for Paxos for a       *)
(* particular instance i and a fixed configuration C.                      *)
(***************************************************************************)
ChosenInBal(i, b, C, cmd) ==
  (*************************************************************************)
  (* True iff command cmd is chosen in ballot b.                           *)
  (*************************************************************************)
  \E Q \in C.quorums : 
    \A a \in Q : Voted(a, i, b, C.cnum, cmd)

ChosenIn(i, C, cmd) == \E b \in BNum : ChosenInBal(i, b, C, cmd) 
  (*************************************************************************)
  (* True iff command cmd is chosen.                                       *)
  (*************************************************************************)

ChoosableAt(i, b, C, cmd) ==
  (*************************************************************************)
  (* True iff command c has been chosen or could still be chosen in ballot *)
  (* b.                                                                    *)
  (*************************************************************************)
  \E Q \in C.quorums : 
    \A a \in Q : \/ Voted(a, i, b, C.cnum, cmd) 
                 \/ avote[a][i][b] = init

UnchoosableBefore(i, b, C, cmd) ==
  (*************************************************************************)
  (* True iff it is not possible for command c ever to be chosen in any    *)
  (* ballot numbered less than b.                                          *)
  (*************************************************************************)
  \A bb \in 0 .. (b-1): ~ ChoosableAt(i, bb, C, cmd)

SafeAt(i, b, C, cmd) ==
  (*************************************************************************)
  (* True iff it is safe for an acceptor to vote for command cmd in ballot *)
  (* b (because no other command can be chosen with a smaller ballot       *)
  (* number).                                                              *)
  (*************************************************************************)
  \A c \in Cmd \ {cmd} : UnchoosableBefore(i, b, C, c)


(***************************************************************************)
(* The following state predicate asserts that it is safe to try to choose  *)
(* a command in ballot b of instance i using configuration C. It assserts  *)
(* that C was learned in some instance ii < i and that in every instance j *)
(* with ii < j < i, no reconfiguration command can possibly be chosen in a *)
(* ballot < b and no acceptor can vote for a reconfiguration command in    *)
(* ballot b.                                                               *)
(***************************************************************************)
ConfigOKAt(i, b, C) ==
  \E ii \in -1 .. (i-1) :
    /\ <<ii, ConfigCmd(C)>> \in learned
    /\ \A j \in (ii+1)..(i-1), c \in CCmd : 
         /\ UnchoosableBefore(j, b, C, c)
         /\ \A a \in Acc : ~Voted(a, j, b, C.cnum, c)
            (***************************************************************)
            (* Note: a ConfigOK formula is used as an enabling condition   *)
            (* in the action by which an acceptor votes.  In practice, the *)
            (* real enabling condition will be the stronger formula        *)
            (*                                                             *)
            (*     \A a \in Acc, n \in BNum : ~ Voted(a, j, b, n, c)       *)
            (*                                                             *)
            (* However, my proof seems to requires the weaker formula.  I  *)
            (* think the algorithm remains correct with the weaker         *)
            (* precondition.                                               *)
            (***************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                                 ACTIONS                                 *)
(*                                                                         *)
(* The following is the action in which acceptor `a' votes in instance i   *)
(* at ballot b for command cmd using configuration numbere cnum.  The      *)
(* first three conjuncts are enabling conditions.  In an implementation,   *)
(* acceptor `a' will perform this action only if it receives of a phase2a  *)
(* message containing i, b, cnum, and cmd from the leader of ballot b.     *)
(* It is up to the leader to ensure that the second and third conjuncts    *)
(* will be satisfied when that message is received.  After preforming the  *)
(* action (meaning after the new value of avote[a][i][b] is written in     *)
(* stable storage), acceptor `a' will send a phase2b message.  The         *)
(* purpose of those phase2b messages is to enable some process to learn    *)
(* if command cmd has been chosen.                                         *)
(***************************************************************************)
VoteFor(a, i, b, cnum, cmd) ==
  /\ (**********************************************************************)
     (* `a' has not already voted or abstained in this ballot.             *)
     (**********************************************************************)
     avote[a][i][b] = init 

  /\ (**********************************************************************)
     (* Any other acceptor that has voted in ballot b of instance i has    *)
     (* voted for cmd with configuration number cnum.                      *)
     (**********************************************************************)
     \A aa \in Acc \ {a} :
       (avote[aa][i][b] \in Vote) =>  
         (avote[aa][i][b] = [cnum |-> cnum, cmd |-> cmd])

  /\ (**********************************************************************)
     (* It is safe to try to choose a command with ballot b in instance i  *)
     (* for some configuration C with number cnum.  Moreover, if cmd is a  *)
     (* reconfiguration command, then no configuration command can ever be *)
     (* chosen with configuration C in any instance after i with a ballot  *)
     (* number < b.                                                        *)
     (**********************************************************************)
     \E C \in Config : 
        /\ C.cnum = cnum
        /\ ConfigOKAt(i, b, C)
        /\ SafeAt(i, b, C, cmd)
        /\ \A newC \in Config : 
              (cmd = ConfigCmd(newC))
                 => /\ newC.cnum = cnum + 1
                    /\ \A ii \in INum, c \in Cmd :
                          (ii > i) => 
                             /\ UnchoosableBefore(ii, b, C, c)
                             /\ \/ ChosenInBal(i, b, C, cmd)
                                \/ \A aa \in Acc :
                                     avote[aa][ii][b] \notin Vote
            (***************************************************************)
            (* When the leader sends the Phase2a message for this vote,    *)
            (* the last disjunct will be true.  However, it can send       *)
            (* Phase2a messages in instance ii once it knows that cmd is   *)
            (* chosen in ballot b.  In that case, the preceding disjunct   *)
            (* will be true when the first Phase2a message arrives at `a'. *)
            (***************************************************************)
                          
  /\ (**********************************************************************)
     (* Set avote[a][i][b] to a vote with configuration number cnum and    *)
     (* command cmd.                                                       *)
     (**********************************************************************)
     avote' = [avote EXCEPT ![a][i][b] = [cnum |-> cnum, cmd |-> cmd]]

  /\ (**********************************************************************)
     (* Leave learned unchanged.                                            *)
     (**********************************************************************)
     UNCHANGED learned

(***************************************************************************)
(* The following action is one in which acceptor `a' abstains (votes       *)
(* `none') for every pair <<i, b>> in the set S of instance number, ballot *)
(* number pairs in which it has not yet voted.  This action is always      *)
(* enabled.  In an actual implementation, acceptor `a' performs this       *)
(* action for the set S equal to the set of <<i, b>> with b < b0 and i any *)
(* instance number when it receives a phase1b message with ballot          *)
(* number b0.  It also performs the action for S the set of all <<i, b>>   *)
(* with b < b0 when it receives a phase2a message for instance i with      *)
(* ballot number b0 before it performs the Vote action.  This action will  *)
(* be a no-op (will perform a stuttering step) if `a' discards the phase1a *)
(* or phase2a message because it has already seen one with a ballow number *)
(* \geq b0.                                                                *)
(***************************************************************************)
Abstain(a, S) ==
  /\ avote' = [avote EXCEPT ![a] =
                 [i \in INum |-> [b \in BNum |-> IF /\ <<i, b>> \in S
                                                    /\ avote[a][i][b] = init
                                                   THEN none
                                                   ELSE avote[a][i][b] ] ] ]
  /\ UNCHANGED learned

(***************************************************************************)
(* The action by which a command cmd is learned in instance i at ballot b. *)
(* It occurs if cmd is chosen for that instance and ballot by a            *)
(* configuration C for which it is safe to choose commands in that         *)
(* instance and ballot.                                                    *)
(***************************************************************************)
Learn(i, b, cmd) ==
  /\ \E C \in Config : /\ ConfigOKAt(i, b, C)
                       /\ ChosenInBal(i, b, C, cmd)
                       /\ learned' = learned \cup {<<i, cmd>>}
  /\ UNCHANGED avote


(***************************************************************************)
(* The next-state action is one that performs any of the Vote, Abstain, or *)
(* Learn steps described above.                                            *)
(***************************************************************************)
Next == \/ \E a \in Acc:
             \/ \E S \in SUBSET (INum \X BNum) : Abstain(a, S) 
             \/ \E i \in INum, b \in BNum, cnum \in CNum, cmd \in Cmd : 
                  VoteFor(a, i, b, cnum, cmd)
        \/ \E i \in INum, b \in BNum, cmd \in Cmd : Learn(i, b, cmd)
-----------------------------------------------------------------------------
(***************************************************************************)
(* The standard TLA+ formula that represents the complete algorithm, with  *)
(* no liveness assumptions on when actions must be performed.              *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<avote, learned>>

(***************************************************************************)
(* The fact that TypeOK is an invariant of the algorithm is expressed      *)
(* formally by:                                                            *)
(***************************************************************************)
THEOREM Spec => []TypeOK

(***************************************************************************)
(* The following is the invariant that expresses the desired safety        *)
(* property, and the theorem asserting that it is an invariant.            *)
(***************************************************************************)
SafetyInv == \A ch1, ch2 \in learned : (ch1[1] = ch2[1]) => (ch1 = ch2)
THEOREM Spec => []SafetyInv
-----------------------------------------------------------------------------

(***************************************************************************)
(* We first prove some stability results.  A predicate P is generally      *)
(* called stable if it can't be made false by executing a step.  When      *)
(* formalized in an untyped system, this generally assumes that the        *)
(* starting state is type-correct.                                         *)
(***************************************************************************)
Stable(P) == TypeOK /\ P /\ Next => P'

THEOREM Stability ==
 /\(*1*)  \A i \in INum, c \in Cmd : Stable(<<i, c>> \in learned)
 /\(*2*)  \A a \in Acc, i \in INum, b \in BNum, n \in CNum, c \in Cmd:
            /\(*2.1*)  Stable( Voted(a, i, b, n, c) )
            /\(*2.2*)  Stable( /\ ~Voted(a, i, b, n, c)
                               /\ avote[a][i][b] # init  )
 /\(*3*)  \A i \in INum, b \in BNum, c \in Cmd, C \in Config: 
            /\(*3.1*)  Stable( ChosenInBal(i, b, C, c) )
            /\(*3.2*)  Stable( ~ChoosableAt(i, b, C, c) )
            /\(*3.3*)  Stable( UnchoosableBefore(i, b, C, c) )
            /\(*3.4*)  Stable( SafeAt(i, b, C, c) )

(***************************************************************************)
(* Proof: 1 and 2 are obvious since no action removes an element from      *)
(* `learned' and once an acceptor has voted or abstained in a ballot, it   *)
(* cannot retract that decision.  The proof of 3 uses 1 and 2 and the fact *)
(* that the conjunction or disjunction (and hence \A and \E) of stable     *)
(* predicates are stable.  The only part that takes a little work is 3.2,  *)
(* which requires first rewriting ~ChoosableAt(i, b, C, c) as              *)
(*                                                                         *)
(*    \A Q \in C.quorums :                                                 *)
(*      \E a \in Q : ~Voted(a, i, b, C.cnum, c) /\ avote[a][i][b] # init   *)
(*                                                                         *)
(* and applying 2.1.                                                       *)
(***************************************************************************)


(***************************************************************************)
(* We define Max(S) to be the maximum of the set S of numbers, if S is     *)
(* non-empty.                                                              *)
(***************************************************************************)
Max(S) == CHOOSE k \in S : \A j \in S : k \geq j


(***************************************************************************)
(* Suppose that m+1 reconfiguration commands have been chosen and they     *)
(* can be numbered C_0, ...  , C_m such that each C_j with j>0 was chosen  *)
(* in ballot b_j of instance i_j using configuration C_(j-1) with          *)
(* i_1 < i_2 < ...  < i_m.  Let i_0 = -1 and b_0 = 0, and let c_j be the   *)
(* command that chooses new configuration C_j.  Then the following         *)
(* definitions define                                                      *)
(*                                                                         *)
(*   maxcfg  = m                                                           *)
(*                                                                         *)
(*   cfgl[j] = <<i_j, c_j>>                                                *)
(*                                                                         *)
(*   cfgi[j] = i_j                                                         *)
(*                                                                         *)
(*   cfgc[j] = c_j                                                         *)
(*                                                                         *)
(*   cfgC[j] = C_j                                                         *)
(*                                                                         *)
(*   cfgb[j] = b_j                                                         *)
(***************************************************************************)
learnedRcfg == { ln \in learned : ln[2] \in CCmd } 
maxcfg == Cardinality(learnedRcfg) - 1
cfgl == [j \in 0..maxcfg |-> CHOOSE ln \in learnedRcfg : ln[2].cnum = j ]
cfgi == [j \in 0..maxcfg |-> cfgl[j][1]]
cfgc == [j \in 0..maxcfg |-> cfgl[j][2]]
cfgC == [j \in 0..maxcfg |-> ConfigOfCmd(cfgc[j])]

RECURSIVE cfgb  \* This statement warns that the definition of cfgb is recursive.
cfgb == [j \in 0..maxcfg |->
          IF j = 0 THEN 0
                   ELSE CHOOSE b \in BNum : 
                          /\ ChosenInBal(cfgi[j], b, cfgC[j-1], cfgc[j])
                          /\ ConfigOKAt(cfgi[j], b, cfgC[j-1])     ]
                        (***************************************************)
                        (* The choice isn't necessarily unique, but it     *)
                        (* doesn't matter which b is chosen.               *)
                        (***************************************************)
                        

(***************************************************************************)
(* The definitions of cfgl, etc. define what they are supposed to only if  *)
(* the set of chosen reconfiguration commands satisfies a certain          *)
(* property.  The following predicate asserts that they really do satisfy  *)
(* those properties.  More precisely, it asserts enough so that those      *)
(* properties follow from it and the definitions.                          *)
(***************************************************************************)
CfgOK ==
  /\ cfgl \in [0..maxcfg -> learnedRcfg]
  /\ cfgb \in [0..maxcfg -> BNum]
  /\ cfgi[0] = -1
  /\ cfgC[0] = InitConfig
  /\ cfgb[0] = 0
  /\ \A j \in 0..maxcfg :  /\ <<cfgi[j], cfgc[j]>> \in learnedRcfg
                           /\ cfgC[j].cnum = j
  /\ \A j \in 1..maxcfg :  /\ ChosenInBal(cfgi[j], cfgb[j], cfgC[j-1], cfgc[j])
                           /\ ConfigOKAt(cfgi[j], cfgb[j], cfgC[j-1])
  /\ \A j \in 1..maxcfg, i \in INum :
         (i > cfgi[j]) => \A c \in Cmd : UnchoosableBefore(i, cfgb[j], cfgC[j-1], c)

(***************************************************************************)
(* The following theorem asserts that the desired properties of cfgi, etc. *)
(* not explicitly stated in CfgOK follow from it and the definitions.      *)
(* (This theorem isn't used explicitly, but it's probably used             *)
(* implicitly.)                                                            *)
(***************************************************************************)
THEOREM TypeOK /\ CfgOK =>
          /\ cfgi \in [0..maxcfg -> INum \cup {-1}] 
          /\ cfgC \in [0..maxcfg -> Config]
          /\ cfgb \in [0..maxcfg -> BNum ]
          /\ \A j\in 0..maxcfg : cfgc[j] = ConfigCmd(cfgC[j])
          /\ learnedRcfg = {cfgl[j] : j \in 0..maxcfg}
  PROOF OBVIOUS

(***************************************************************************)
(* The following stability property is used in the invariance proof.       *)
(***************************************************************************)
THEOREM CfgStability ==
    CfgOK => 
       \A i \in INum, b \in BNum, C \in Config :
         /\ \A a \in Acc, c \in Cmd : Stable( /\ Voted(a, i, b, C.cnum, c)
                                              /\ ConfigOKAt(i, b, C)  )
         /\ \A c \in Cmd : Stable( /\ ChosenInBal(i, b, C, c)
                                   /\ ConfigOKAt(i, b, C)  )

<1>1 HAVE CfgOK
  (*************************************************************************)
  (* This statement means that we're assuming CfgOK and proving the        *)
  (* formula that it's supposed to imply.                                  *)
  (*************************************************************************)
  
<1>2. TAKE i \in INum, b \in BNum, C \in Config
  (*************************************************************************)
  (* This statement means that our current goal is a formula of the form   *)
  (*                                                                       *)
  (*   \A i \in INum, b \in BNum, C \in Config : P                         *)
  (*                                                                       *)
  (* and we're going to prove it by introducing these new constants i, b,  *)
  (* and C and proving P.                                                  *)
  (*************************************************************************)
  

<1>3. ASSUME CONSTANT a \in Acc, 
             CONSTANT c \in Cmd
      PROVE Stable( /\ Voted(a, i, b, C.cnum, c)
                    /\ ConfigOKAt(i, b, C)  )

  <2>1. SUFFICES ASSUME Next, Voted(a, i, b, C.cnum, c), 
                        ConfigOKAt(i, b, C)
                 PROVE  ConfigOKAt(i, b, C)'

    (***********************************************************************)
    (* Note: This statement is read "it suffices to assume ... and         *)
    (*       prove ..."                                                    *)
    (*                                                                     *)
    (* Proof: By definition of stability and the fact that Voted(...)  is  *)
    (* stable.                                                             *)
    (***********************************************************************)
  <2>2. PICK ii \in -1 .. (i-1) :
             /\ <<ii, ConfigCmd(C)>> \in learned
             /\ \A j \in (ii+1)..(i-1), c4 \in CCmd : 
                  /\ UnchoosableBefore(j, b, C, c4)
                  /\ \A aa \in Acc : ~ Voted(aa, j, b, C.cnum, c4)
    (***********************************************************************)
    (* By the assumption ConfigOKAt(...)  of <2>1 and the definition of    *)
    (* ConfigOKAt.                                                         *)
    (***********************************************************************)
    
  <2>3. SUFFICES ASSUME CONSTANT j \in (ii+1)..(i-1), 
                        CONSTANT c4 \in CCmd,
                        CONSTANT aa \in Acc,
                        ~ Voted(aa, j, b, C.cnum, c4),
                        Voted(aa, j, b, C.cnum, c4)'
                 PROVE  FALSE
    (***********************************************************************)
    (* Proof: By <2>1 we're assuming ConfigOKAt(i, b, C) and have to prove *)
    (* ConfigOKAt(i, b, C)'.  ConfiguOKAt(...)  is the disjunction and     *)
    (* conjunction of formulas all of which are stable except for          *)
    (*                                                                     *)
    (*   \A a \in Acc: ~ Voted(a, j, b, C.cnum, c),                        *)
    (*                                                                     *)
    (* So we just have to show that ~ Voted(aa, j, b, n, c4) is stable for *)
    (* every aa, j, c4, and n.  The proof is by contradiction.             *)
    (***********************************************************************)
    
  <2>4. VoteFor(aa, j, b, C.cnum, c4) 
     (**********************************************************************)
     (* Proof: By the assumptions of <2>3, because this VoteFor action is  *)
     (* the only subaction of Next that can make                           *)
     (* Voted(aa, j, b, C.cnum, c) become true.                            *)
     (**********************************************************************)
     
  <2>5. PICK CC \in Config : 
           /\ CC.cnum = C.cnum
           /\ ConfigOKAt(j, b, CC)
           /\ ChosenInBal(j, b, CC, c4)
     (**********************************************************************)
     (* Proof: The required CC exists by <2>4 and the third conjunct of    *)
     (* VoteFor(aa, j, b, C.cnum, c4), using the assumption c4 \in CCmd of *)
     (* <2>3 and the assumption Voted(a, i, b, C.cnum, c) of <2>1, which   *)
     (* implies avote[a][i][b] \in Vote, so the final disjunct at the end  *)
     (* of that conjunct is false.                                         *)
     (**********************************************************************)

  <2>6. CC = C
     (**********************************************************************)
     (* This follows from ConfigOKAt(j, b, CC) (from <2>5) and             *)
     (* ConfigOKAt(i, b, C) (from <2>1, which imply that ConfigCmd(CC) and *)
     (* ConfigCmd(C) are both learned commands.  It then follows from      *)
     (* CC.cnum = C.cnum (from <2>5) and CfigOK (<1>1), which implies that *)
     (* chosen reconfiguration commands have unique numbers, that CC = C.  *)
     (**********************************************************************)

  <2>7. \A a3 \in Acc : ~Voted(a3, j, b, C.cnum, c4)
    (***********************************************************************)
    (* Proof: By the last conjunct of <2>2, since <2>3 implies             *)
    (* j \in (ii+1)..(i-1) and c4 \in CCmd                                 *)
    (***********************************************************************)
    
  <2>8. QED
    (***********************************************************************)
    (* Proof: ChosenInBal(j, b, CC, c4) (from <2>5) implies Voted(aa, b,   *)
    (* CC.cnum, c4) aa.  By <2>6 (CC = C), this contradicts <2>7.          *)
    (***********************************************************************)
    
<1>4. ASSUME CONSTANT c1 \in Cmd   \* Bug in parser prevents reuse of symbol c
      PROVE  Stable( /\ ChosenInBal(i, b, C, c1)
                      /\ ConfigOKAt(i, b, C)  )
  (*************************************************************************)
  (* Proof: Since ChosenInBal(i, b, C, c1) implies                         *)
  (* Voted(a, i, b, C.cnum, c1), for some `a', this follows easily from    *)
  (* <1>3 and the stability of ChosenInBal(i, b, C, c1).                   *)
  (*************************************************************************)
  BY <1>4!2 + 1
  
<1>5. QED
  BY <1>1, <1>2, <1>3, <1>4
-----------------------------------------------------------------------------

(***************************************************************************)
(* We now define the inductive invariant that is the heart of the safety   *)
(* proof.                                                                  *)
(***************************************************************************)
Inv ==
 /\(*1*)  TypeOK 

 /\(*2*)  \A a \in Acc, i \in INum, b \in BNum, n \in CNum, c \in Cmd :
            Voted(a, i, b, n, c) =>
                   \A aa \in Acc, nn \in CNum, cc \in Cmd :
                      Voted(aa, i, b, nn, cc) => (<<nn, cc>> = <<n, c>>)

 /\(*3*)  \A i \in INum, c \in Cmd :
             (<<i, c>> \in learned) => 
               \E b \in BNum, C \in Config : /\ ConfigOKAt(i, b, C)
                                             /\ ChosenInBal(i, b, C, c)

 /\(*4*)  CfgOK

 /\(*5*)  \A a \in Acc, i \in INum, b \in BNum, n \in CNum, c \in Cmd :
            Voted(a, i, b, n, c) => 
              \E C \in Config :
                /\ C.cnum = n
                /\ ConfigOKAt(i, b, C)
                /\ SafeAt(i, b, C, c)
                /\ c \in CCmd => /\ ConfigOfCmd(c).cnum = n+1
                                 /\ \A j \in INum, cc \in Cmd :
                                       (j > i) => UnchoosableBefore(j, b, C, cc)
                /\ ChoosableAt(i, b, C, c) =>
                     C = cfgC[ Max({j \in 0..maxcfg : cfgi[j] < i}) ]


(***************************************************************************)
(* We first prove that this Inv is strong enough--that is, it implies the  *)
(* predicate that we want to show is invariant.                            *)
(***************************************************************************)
THEOREM Inv => SafetyInv

<1>1. SUFFICES ASSUME Inv,
                      CONSTANT i \in INum,
                      CONSTANT c1 \in Cmd,
                      CONSTANT c2 \in Cmd,
                      <<i, c1>> \in learned /\ <<i, c2>> \in learned
               PROVE  c1 = c2
  PROOF OBVIOUS

<1>2. PICK C1, C2 \in Config, b1, b2 \in BNum :
        /\ ConfigOKAt(i, b1, C1)
        /\ ChosenInBal(i, b1, C1, c1)
        /\ ConfigOKAt(i, b2, C2)
        /\ ChosenInBal(i, b2, C2, c2)
  (*************************************************************************)
  (* Proof: By <<i, c1>> and <<i, c2>> in `learned' (from <1>1) and Inv!3 *)
  (* (which is assumed by <1>1).                                           *)
  (*************************************************************************)

<1>3. PICK a1, a2 \in Acc : /\ Voted(a1, i, b1, C1.cnum, c1)
                            /\ Voted(a2, i, b2, C2.cnum, c2)        
  (*************************************************************************)
  (* Proof: By <1>2, since ChosenInBal implies at least one vote.          *)
  (*************************************************************************)

<1>4. PICK CC1, CC2 \in Config :  
        /\ CC1.cnum = C1.cnum
        /\ ConfigOKAt(i, b1, CC1)
        /\ ChoosableAt(i, b1, CC1, c1) =>
              CC1 = cfgC[Max ({j \in 0 .. maxcfg : cfgi[j] < i})]
        /\ CC2.cnum = C2.cnum
        /\ ConfigOKAt(i, b2, CC2)
        /\ ChoosableAt(i, b2, CC2, c2) =>
              CC2 = cfgC[Max ({j \in 0 .. maxcfg : cfgi[j] < i})]
  (*************************************************************************)
  (* Proof: By <1>3 and conjunction 5 of Inv.                             *)
  (*************************************************************************)

<1>5. (CC1 = C1) /\ (CC2 = C2)
  (*************************************************************************)
  (* Proof: ConfigOKAt(i, b1, C1) (1st conjunct of <1>2) and               *)
  (* ConfigOKAt(i, b1, CC1) (2nd conjunct of <1>4) imply that <<i1, C1>>   *)
  (* and <<ii1, CC1>> are in `learned' for some i1 and ii1, and C1.cnum =  *)
  (* CC1.cnum (<1>4!1).  By CfgOK, this implies that C1 = CC1.  Similarly, *)
  (* C2 = CC2.                                                             *)
  (*************************************************************************)

<1>6.  C1 = C2 
  (*************************************************************************)
  (* Proof: We have ChosenInBal(i, b1, C1, c1) (second conjunct of <1>2),  *)
  (* which by definition of ChosenInBal and ChoosableAt implies            *)
  (* ChoosableAt(i, b1, C1, c1).  By <1>5 and the 3rd conjunct of <1>4,    *)
  (* this shows that                                                       *)
  (*                                                                       *)
  (*    C1 = cfgC[Max ({j \in 0 .. maxcfg : cfgi[j] < i})]                 *)
  (*                                                                       *)
  (* A similar argument shows that C2 equals the same expression.          *)
  (*************************************************************************)

<1>7. QED
  (*************************************************************************)
  (* Proof: <1>6 and <1>2 imply ChosenInBal(i, b1, C, c1) and              *)
  (* ChosenInBal(i, b2, C, c2) for C = C1 = C2.  The same simple reasoning *)
  (* used in the proof of ordinary Paxos (with a fixed configuration C)    *)
  (* shows that this implies c1 = c2.                                      *)
  (*************************************************************************)
-----------------------------------------------------------------------------

(***************************************************************************)
(* Here is the heart of the proof--the proof that Inv is an inductive      *)
(* invariant.                                                              *)
(***************************************************************************)
THEOREM InductiveInvariance == Inv /\ Next => Inv'
<1>1. HAVE Inv /\ Next

<1>2. Inv!1'
  (*************************************************************************)
  (* It is straighforward to show that TypeOK /\ Next => TypeOK'.          *)
  (*************************************************************************)

\* <1> USE TypeOK
\* On 4 Mar 2009 it became illegal to use arbitrary expressions as
\* facts in a USE or HIDE--making this USE illegal

<1>2a. TypeOK
  PROOF OBVIOUS
<1> USE <1>2a  
  (*************************************************************************)
  (* This statement means that from now on, we are free to use TypeOK      *)
  (* without explicitly mentioning that we're using it.  In an informal    *)
  (* proof like this one, there are undoubtedly lots of places where we    *)
  (* assume other things without mentioning them.  If we've been careful,  *)
  (* then we haven't assumed anything that we're not allowed to.           *)
  (*************************************************************************)
  
<1>3. Inv!2' 
  (*************************************************************************)
  (* Proof: Next and Inv!2 true and Inv!2' false implies that              *)
  (* VoteFor(a1, i, b, n, c) /\ Voted(a2, i, b, nn, cc) is true for some   *)
  (* a2 # a1 and cc # c.  The second conjunct of VoteFor(a1, i, b, n, c)   *)
  (* implies that this is impossible.                                      *)
  (*************************************************************************)
  
<1>4. Inv!3'
  (*************************************************************************)
  (* Proof: Next and Inv!3 true and Inv!3' false implies that there is     *)
  (* some i, bb, and c such that Learn(i, bb, c) is true but               *)
  (*                                                                       *)
  (*   \E b \in BNum, C \in Config : /\ ConfigOKAt(i, b, C)                *)
  (*                                 /\ ChosenInBal(i, b, C, c)            *)
  (*                                                                       *)
  (* is false.  The definition of Learn(i, bb, c) implies that this is     *)
  (* impossible.                                                           *)
  (*************************************************************************)
  
<1>5. Inv!4' 
  <2>1. CASE learnedRcfg' = learnedRcfg
    <3>1. maxcfg' = maxcfg /\ cfgl' = cfgl
      (*********************************************************************)
      (* Proof: By case assumption <2>1 becuase maxcfg is defined in terms *)
      (* of learnedRcfg and cfgl is defined in terms of maxcfg and         *)
      (* learnedRcfg.                                                      *)
      (*********************************************************************)
    <3>2. cfgi' = cfgi /\ cfgc' = cfgc /\ cfgC' = cfgc /\ cfgb' = cfgb
      (*********************************************************************)
      (* Proof: By <3>1, since All these values are defined in terms of    *)
      (* cfgl and maxcfg.                                                  *)
      (*********************************************************************)
    <3>3. QED
      (*********************************************************************)
      (* Proof: CfgOK' follows by assumption <2>1, <3>1, <3>2, the         *)
      (* stability of                                                      *)
      (*                                                                   *)
      (*   /\ ChosenInBal(cfgi[j], cfgb[j], cfgC[j-1], cfgc[j])            *)
      (*   /\ ConfigOKAt(cfgi[j], cfgb[j], cfgC[j-1])                      *)
      (*                                                                   *)
      (* for all j (by <1>1 and Theorem CfgStability) and the stability of *)
      (*                                                                   *)
      (*   UnchoosableBefore(i, cfgb[j], cfgC[j-1], c)                     *)
      (*                                                                   *)
      (* for all j, c (by Theorem Stability).                              *)
      (*********************************************************************)
       
  <2>2. CASE learnedRcfg' # learnedRcfg 

    <3>1. PICK i \in INum, b \in BNum, C \in Config : Learn(i, b, ConfigCmd(C))
      (*********************************************************************)
      (* Proof: Case assumption <2>2 and the definition of Next.           *)
      (*********************************************************************)
    <3>  DEFINE c == ConfigCmd(C)
      
    <3>2. PICK k \in 0..maxcfg :
            /\ ConfigOKAt(i, b, cfgC[k])
            /\ ChosenInBal(i, b, cfgC[k], c)
            /\ learned' = learned \cup {<<i, c>>}
      (*********************************************************************)
      (* Proof: By <3>1, the definition of Learn, and CfgOK (Inv!4), which *)
      (* implies that the configuration whose existence is implied by the  *)
      (* definition Learn(i, b, c) must be one of the cfgC[j].             *)
      (*********************************************************************)
   <3>3. i > cfgi[k]
     (**********************************************************************)
     (* Proof: By ChosenInBal(i, b, cfgC[k], c) (<3>2), definition of      *)
     (* ConfigOKAt, and CfgOK                                              *)
     (**********************************************************************)
      
   <3>4. k = maxcfg
      <4>1. SUFFICES ASSUME k < maxcfg
                     PROVE  FALSE
        (*******************************************************************)
        (* Proof by contradiction.                                         *)
        (*******************************************************************)

      <4> HAVE k < maxcfg

      <4>2. CASE i > cfgi[k+1]
        <5>1. b < cfgb[k+1]
          <6>1. /\ UnchoosableBefore(cfgi[k+1], b, cfgC[k], cfgc[k+1])      
                /\ \A a \in Acc: ~Voted(a, cfgi[k+1], b, cfgC[k].cnum, cfgc[k+1])
            (***************************************************************)
            (* Proof: By ConfigOKAt(i, b, cfgC[k]) (<3>2), case assumption *)
            (* <4>2, and cfgi[k] < cfgi[k+1] (by CfgOK).                   *)
            (***************************************************************)
          <6>2. QED
            (***************************************************************)
            (* Proof: Since CfgOK implies                                  *)
            (*                                                             *)
            (*     ChosenInBal(cfgi[k+1], cfgb[k+1], cfgC[k], cfgc[k+1])   *)
            (*                                                             *)
            (* <6>1 implies that cfgb[k+1] cannot be \leq b.               *)
            (***************************************************************)

        <5>2. UnchoosableBefore(i, cfgb[k+1], cfgC[k], c)
          (*****************************************************************)
          (* Proof: By the last conjunct of CfgOK, substituting k+1 for j, *)
          (* using case assumption <4>2.                                   *)
          (*****************************************************************)

        <5>3. QED
          (*****************************************************************)
          (* Proof: <5>1 and <5>2 contradict <3>2, which implies           *)
          (* ChosenInBal(i, b, cfgC[k], c).                                *)
          (*****************************************************************)
          
      <4>3. CASE i < cfgi[k+1]
        <5>1. b > cfgb[k+1]
          <6>1. /\ UnchoosableBefore(i, cfgb[k+1], cfgC[k], c)
                /\ \A a \in Acc : ~Voted(a, i, cfgb[k+1], cfgC[k].cnum, c)
            (***************************************************************)
            (* Proof: By CfgOK, which implies                              *)
            (* ConfigOKAt(cfgi[k+1], cfgb[k+1], cfgC[k]) and the           *)
            (* definition of ConfigOKAt, since case assumption <4>3 and    *)
            (* <3>3 allows us to substitute i for j in the definition.     *)
            (***************************************************************)
          <6>2. QED
            (***************************************************************)
            (* Proof: <3>2 implies ChosenInBal(i, b, cfgC[k], c), which    *)
            (* would contradict <6>1 if b \leq cfgb[k+1].                  *)
            (***************************************************************)

        <5>2. PICK a \in Acc : Voted(a, i, b, cfgC[k].cnum, c)
          (*****************************************************************)
          (* Proof: By ChosenInBal(i, b, cfgC[k], c) (from <3>2).          *)
          (*****************************************************************)
          
        <5>3. PICK CC \in Config :
                /\ CC.cnum = cfgC[k].cnum
                /\ ConfigOKAt(i, b, CC)
                /\ UnchoosableBefore(cfgi[k+1], b, CC, cfgc[k+1])
          (*****************************************************************)
          (* Proof: By <5>2 and the Inv!5, using case assumption <4>3 to   *)
          (* justify substituting cfgc[k+1] for j in the 4th conjunct of   *)
          (* the body of the \E C \in Config expression.                   *)
          (*****************************************************************)

        <5>4. CC = cfgC[k]          
          (*****************************************************************)
          (* Proof: ConfigOKAt(i, b, CC) (from <5>3) and CfgOK implies CC  *)
          (* equals cfgC[j] for some j, and CC.cnum = cfgC[k].cnum (from   *)
          (* <5>3) implies j = k.                                          *)
          (*****************************************************************)

        <5>5. QED 
          (*****************************************************************)
          (* Proof: <5>3 and <5>4 imply                                    *)
          (*                                                               *)
          (*      UnchoosableBefore(cfgi[k+1], b, cfg[k], cfgc[k+1])       *)
          (*                                                               *)
          (* and by b > cfgb[k+1] (from <5>1) this contradicts CfgOK,      *)
          (* which implies                                                 *)
          (*                                                               *)
          (*      ChosenInBal(cfgi[k+1], cfgb[k+1], cfgC[k], cfgc[k+1])    *)
          (*****************************************************************)
          
      <4>4. CASE i = cfgi[k+1]
        <5>1. ChosenInBal(i, b, cfgC[k], c)
          BY <3>2

        <5>2. ChosenInBal(cfgi[k+1], cfgb[k+1], cfgC[k], cfgc[k+1])
          BY CfgOK

        <5>3. c = cfgc[k+1]
          (*****************************************************************)
          (* Proof: By same simple reasoning used to prove the consistency *)
          (* of ordinary Paxos (for instance i = cfgi[k+1] and the (fixed) *)
          (* configuration cfgC[k]).                                       *)
          (*****************************************************************)

        <5>4. QED
          (*****************************************************************)
          (* Proof: CfgOK implies <<cfgi[k+1], cfgc[k+1]>> \in `learned',  *)
          (* so Learn(i, b, c) implies that `learned' is unchanged,        *)
          (* contradicting case assumption <2>2 (learnedRcfg' #            *)
          (* learnedRcfg).                                                 *)
          (*****************************************************************)
          
      <4>5. QED        
        BY <4>2, <4>3, <4>4

    <3>5. /\(*1*)  <<i, c>> \in learned' \ {learned}
          /\(*2*)  C.cnum = maxcfg + 1
          /\(*3*)  ChosenInBal(i, b, cfgC[maxcfg], c)
          /\(*4*)  ConfigOKAt(i, b, cfgC[maxcfg])
          /\(*5*)  \A ii \in INum :
                     (ii > i) => 
                        \A cc \in Cmd : UnchoosableBefore(ii, b, cfgC[maxcfg], cc)
      <4>1.  <3>5!1
        (*******************************************************************)
        (* Proof: By <3>1 and case assumption <2>2.                        *)
        (*******************************************************************)
        
      <4>2.  <3>5!3
        BY <3>2

      <4>3.  <3>5!4
        BY <3>2

      <4>4. /\ C.cnum = cfgC[maxcfg].cnum + 1
            /\ \A ii \in INum, cc \in Cmd :
                  (ii > i) => UnchoosableBefore(ii, b, cfgC[maxcfg], cc)

        <5>1. PICK a \in Acc : Voted(a, i, b, cfgC[maxcfg], c)
          BY <4>2
        <5>2. PICK CC \in Config :
                /\ CC.cnum = cfgC[maxcfg]
                /\ ConfigOKAt(i, b, CC)
                /\ C.cnum = cfgC[maxcfg].cnum + 1
                /\ \A j \in INum, cc \in Cmd :
                      (j > i) => UnchoosableBefore(j, b, CC, cc)
          (*****************************************************************)
          (* Proof: By <5>1 and Inv!5, since c \in CCmd and C =            *)
          (* ConfigOfCmd(c).                                               *)
          (*****************************************************************)
        <5>3. CC = cfgC[maxcfg]
          (*****************************************************************)
          (* Proof: BY <5>2, since ConfigOKAt(i, b, CC) implies            *)
          (* <<j, CmdOfConfig(CC)>> in `learned', so it equals cfgC[j] for *)
          (* some j, and CC.cnum = cfgC[maxcfg] implies j = maxcfg.        *)
          (*****************************************************************)
        <5>4. QED
          BY <5>2, <5>3
          
      <4>5. <3>5!5

      <4>6. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5

    <3>6. QED
      (*********************************************************************)
      (* Proof: <3>5!1 and <3>5!2 imply that maxcfg' = maxcfg+1 and        *)
      (*                                                                   *)
      (*   cfgl' = [j \in 0..maxcfg' |->                                   *)
      (*              IF j < maxcfg THEN cfgl[j] ELSE <<i, c>>]            *)
      (*                                                                   *)
      (* from which it follows that the functions cfgi', cfgc', cfgC',     *)
      (* and cfgb' are the expected "extensions" of cfgi, cfgc, cfgC, and  *)
      (* cfgb, where <3>5!3 and <3>5!4 imply the existence of the b in     *)
      (* BNum satisfying the CHOOSE expression in the definition of        *)
      (* cfgb'[maxcfg'].  This proves the first 5 conjuncts of CfgOK'.     *)
      (* The remaining three conjuncts are all \A j formulas.  For j <     *)
      (* maxcfg', they follow from CfgOK. For j = maxcfg', they follow     *)
      (* from <3>5.                                                        *)
      (*********************************************************************)
  <2>3. QED
    BY <2>1, <2>2

<1>6. Inv!5'
  <2>1. TAKE a \in Acc, i \in INum, b \in BNum, n \in CNum, c \in Cmd 
  <2>2. HAVE Voted(a, i, b, n, c)'
  <2>3. CASE Voted(a, i, b, n, c)
    (***********************************************************************)
    (* Proof: This case follows from the Theorems Stability and            *)
    (* CfgStability, which imply the stability of all the non-constant     *)
    (* subformuulas in the \E C \in Config expression in Inv!5.            *)
    (***********************************************************************)
  <2>4. CASE ~Voted(a, i, b, n, c)
    <3>1. VoteFor(a, i, b, n, c)
      (*********************************************************************)
      (* Proof: Next, <2>2 and case assumption <2>4, implies this VoteFor  *)
      (* action.                                                           *)
      (*********************************************************************)
      
    <3>2. SUFFICES  (* to prove *)
            \E C \in Config :
                /\ C.cnum = n
                /\ ConfigOKAt(i, b, C)
                /\ SafeAt(i, b, C, c)
                /\ c \in CCmd => /\ ConfigOfCmd(c).cnum = n+1
                                 /\ \A j \in INum, cc \in Cmd :
                                       (j > i) => UnchoosableBefore(j, b, C, cc)
                /\ ChoosableAt(i, b, C, c) =>
                     C = cfgC[ Max({j \in 0..maxcfg : cfgi[j] < i}) ]
      (*********************************************************************)
      (* Proof: For all other tuples <<aa, ii, bb, nn, cc>>, the body of   *)
      (* the \A of Inv!5' follows from Inv!5 and Theorems Stability and    *)
      (* CfgStability.                                                     *)
      (*********************************************************************)

    <3>3. PICK C \in Config :
            /\ C.cnum = n
            /\ ConfigOKAt(i, b, C)
            /\ SafeAt(i, b, C, c)
            /\ c \in CCmd => /\ ConfigOfCmd(c).cnum = n+1
                             /\ \A j \in INum, cc \in Cmd :
                                       (j > i) => UnchoosableBefore(j, b, C, cc)
      (*********************************************************************)
      (* Proof: The existence of C follows from <3>1 and the definition of *)
      (* VoteFor.                                                          *)
      (*********************************************************************)

    <3>4. ASSUME ChoosableAt(i, b, C, c),
                 C # cfgC[ Max({j \in 0..maxcfg : cfgi[j] < i}) ]
          PROVE  FALSE
      <4>1. PICK j \in 0..maxcfg : C = cfgC[j]
        (*******************************************************************)
        (* Proof: By CfgOK and ConfigOKAt(i, b, C), which imply that C is  *)
        (* one of the cfgC[j], and                                         *)
        (*******************************************************************)
      <4>2. i > cfgi[j]
        (*******************************************************************)
        (* Proof: <3>3 and <4>1 imply ConfigOKAt(i, b, cfgC[j]), which     *)
        (* implies i > cfgi[j].                                            *)
        (*******************************************************************)
      <4>3. i > cfgi[j+1]
        (*******************************************************************)
        (* Proof: <4>1, <4>2, and the assumption <3>4!2.                   *)
        (*******************************************************************)
      <4>4. cfgb[j+1] > b
        (*******************************************************************)
        (* Proof: Since and i > cfgi[j+1] > cfgi[j] (by <4>3 and CfgOK),   *)
        (* ConfigOKAt(i, b, cfgC[j]) (which holds by <3>3 and <4>1)        *)
        (* implies UnchoosableBefore(cfgi[j+1], b, cfgC[j], cfgc[j+1]) and *)
        (* ~ChosenInBal(cfgi[j+1], b, cfgC[j], cfgc[j+1]).  Since CfgOK    *)
        (* implies ChosenInBal(cfgi[j+1], cfgb[j+1], cfgC[j], cfgc[j+1]),  *)
        (* we cannot have b \geq cfgb[j+1].                                *)
        (*******************************************************************)
      <4>5. QED
        (*******************************************************************)
        (* Proof: The last conjunct of CfgOK implies                       *)
        (*                                                                 *)
        (*   UnchoosableBefore(i, cfgb[j+1], cfgC[j], c)                   *)
        (*                                                                 *)
        (* By <4>4 and <4>1, this contradicts ChoosableAt(i, b, C, c),     *)
        (* which is assumption <3>4!1.                                     *)
        (*******************************************************************)
    <3>5. QED
      BY <3>2, <3>3, <3>4
      
  <2>5. QED
    BY <2>3, <2>4

<1>7. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 

=============================================================================


TLA+2 problems:

 - Can't use "!" selectors to name "c \in S" in 
   ASSUME CONSTANT c \in S
   PARTIALLY FIXED 10 Oct 2007 to allow "CONSTANT c \in S" to
   be used as a fact.

 - <i>j. PICK x ...  makes x declared in the proof of <i>j, which
   is wrong, since it's not legal to use it there.
   FIXED 10 Oct 2007

 - For subexpression naming, PICK is treated like a \A, even though
   the variables being picked are being declared externally to the
   expression.  Thus, we have to write

    <3>4. PICK x : P(x)
    <3>5. ...
      BY <3>4!(x)  \* This names P(x)

   This seems wrong, since x is declared in the scope of the use.
   However, the !(x) can't be omitted if we want to refer to P inside
   the proof of <3>4.  Since we don't want the naming convention to
   depend on where the name appears, we don't have much choice but to
   let it stand as is.

 - Doesn't allow labels in numbered steps.  This seems to be a bug,
   since the parser allows positional naming of subexpressions of
   a numbered step.  FIXED 10 Oct 2007

 - Bug: declaration of NEWs introduced in an ASSUME/PROVE step leak
   out into the rest of the proof.  (They should only for a 
   SUFFICE ASSUME/PROVE step.) FIXED 10 Oct 2007

 - Bug: The error message for duplicate step numbers reports the position
   as the entire containing proof body, not the step.  This indicates
   that some semantic node is being created with the entire proof body
   rather than just its own part of the spec as its syntactic node.
   FIXED 10 Oct 2007
=============================================================================
