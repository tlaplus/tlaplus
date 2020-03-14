------------------------------ MODULE PcalPaxos ----------------------------- 
EXTENDS Integers, TLC, FiniteSets

CONSTANTS Acceptor, Leader, Learner, Ballot, LeaderOf, Command, Majority

ASSUME /\ LeaderOf \in [Ballot -> Leader]
       /\ Ballot \subseteq Nat
       /\ 0 \in Ballot
       /\ Majority \subseteq SUBSET Acceptor
       /\ \A M1, M2 \in Majority : M1 \cap M2 # {}

NotACmd == CHOOSE c : c \notin Command

BallotsOf(ldr) == {b \in Ballot : LeaderOf[b] = ldr}

Message == [type : {"1a"}, bal : Ballot] \cup
           [type : {"1b"}, bal : Ballot, acc : Acceptor,
            mbal : Ballot \cup {-1}, mcmd : Command \cup {NotACmd}] 
              \cup
           [type : {"2a"}, bal : Ballot, cmd : Command]  \cup
           [type : {"2b"}, bal : Ballot, cmd : Command, acc : Acceptor] 

(*
--algorithm Paxos
  variables msgs = {}; 
  macro Send(m) 
   begin msgs := msgs \cup {m}
   end macro

  process Ldr \in Leader
    variables ldrBal = -1 ;
              ldrPhs = 2 
    begin L: 
      while TRUE do
        with b \in {bb \in Ballot : LeaderOf[bb] = self}
          do either when ldrBal < b;
                    ldrBal := b ;
                    ldrPhs := 1 ;
                    Send([type |-> "1a", bal |-> b])

             or     when (ldrBal = b) /\ (ldrPhs = 1) ;
                    with M = {m \in msgs : (m.type = "1b") /\ (m.bal = b)};
                         A = {m.acc : m \in M} ;
                         mmsg \in {m \in M : 
                                    \A m2 \in M : m.mbal \geq m2.mbal}
                       do when A \in Majority ;
                          if mmsg.mbal > -1
                            then Send([type |-> "2a", bal |-> b, 
                                       cmd |-> mmsg.mcmd])
                            else with c \in Command
                                   do Send([type |-> "2a", bal |-> b, 
                                            cmd |-> c])
                                 end with
                          end if ;
                     end with ;
                     ldrPhs := 2
                end either
             end with
      end while
    end process

  process Acc \in Acceptor
    variables bal = -1 ; mbal = -1 ; mcmd = NotACmd
    begin A: 
      while TRUE do 
        with m \in msgs
          do either when (m.type = "1a") /\ (m.bal > bal) ;
                    bal := m.bal ;
                    Send([type |-> "1b", bal |-> m.bal, acc |-> self,
                          mbal |-> mbal, mcmd |-> mcmd])
             or     when    (m.type = "2a")
                         /\ (m.bal \geq bal) 
                         /\ (m.bal > mbal);
                    bal  := m.bal ;
                    mbal := m.bal ;
                    mcmd := m.cmd ;
                    Send([type |-> "2b", bal |-> m.bal, acc |-> self,
                           cmd |-> m.cmd])
             end either
        end with
      end while
    end process


  process Lrn \in Learner
    variable learned = NotACmd
    begin N: with b \in Ballot ;
                  2bMsgs = {m \in msgs : (m.type = "2b") /\ (m.bal = b)}
               do when {m.acc : m \in 2bMsgs} \in Majority ;
                  with m \in 2bMsgs
                    do learned := m.cmd
                  end with
             end with ;
    end process
end algorithm
*)

\* BEGIN TRANSLATION
VARIABLES msgs, pc, ldrBal, ldrPhs, bal, mbal, mcmd, learned

vars == << msgs, pc, ldrBal, ldrPhs, bal, mbal, mcmd, learned >>

ProcSet == (Leader) \cup (Acceptor) \cup (Learner)

Init == (* Global variables *)
        /\ msgs = {}
        (* Process Ldr *)
        /\ ldrBal = [self \in Leader |-> -1]
        /\ ldrPhs = [self \in Leader |-> 2]
        (* Process Acc *)
        /\ bal = [self \in Acceptor |-> -1]
        /\ mbal = [self \in Acceptor |-> -1]
        /\ mcmd = [self \in Acceptor |-> NotACmd]
        (* Process Lrn *)
        /\ learned = [self \in Learner |-> NotACmd]
        /\ pc = [self \in ProcSet |-> CASE self \in Leader -> "L"
                                        [] self \in Acceptor -> "A"
                                        [] self \in Learner -> "N"]

L(self) == /\ pc[self] = "L"
           /\ \E b \in {bb \in Ballot : LeaderOf[bb] = self}:
                \/ /\ ldrBal[self] < b
                   /\ ldrBal' = [ldrBal EXCEPT ![self] = b]
                   /\ ldrPhs' = [ldrPhs EXCEPT ![self] = 1]
                   /\ msgs' = (msgs \cup {([type |-> "1a", bal |-> b])})
                \/ /\ (ldrBal[self] = b) /\ (ldrPhs[self] = 1)
                   /\ LET M == {m \in msgs : (m.type = "1b") /\ (m.bal = b)} IN
                        LET A == {m.acc : m \in M} IN
                          \E mmsg \in {m \in M :
                                        \A m2 \in M : m.mbal \geq m2.mbal}:
                            /\ A \in Majority
                            /\ IF mmsg.mbal > -1
                                  THEN /\ msgs' = (msgs \cup {([type |-> "2a", bal |-> b,
                                                                cmd |-> mmsg.mcmd])})
                                  ELSE /\ \E c \in Command:
                                            msgs' = (msgs \cup {([type |-> "2a", bal |-> b,
                                                                  cmd |-> c])})
                   /\ ldrPhs' = [ldrPhs EXCEPT ![self] = 2]
                   /\ UNCHANGED ldrBal
           /\ pc' = [pc EXCEPT ![self] = "L"]
           /\ UNCHANGED << bal, mbal, mcmd, learned >>

Ldr(self) == L(self)

A(self) == /\ pc[self] = "A"
           /\ \E m \in msgs:
                \/ /\ (m.type = "1a") /\ (m.bal > bal[self])
                   /\ bal' = [bal EXCEPT ![self] = m.bal]
                   /\ msgs' = (msgs \cup {([type |-> "1b", bal |-> m.bal, acc |-> self,
                                            mbal |-> mbal[self], mcmd |-> mcmd[self]])})
                   /\ UNCHANGED <<mbal, mcmd>>
                \/ /\    (m.type = "2a")
                      /\ (m.bal \geq bal[self])
                      /\ (m.bal > mbal[self])
                   /\ bal' = [bal EXCEPT ![self] = m.bal]
                   /\ mbal' = [mbal EXCEPT ![self] = m.bal]
                   /\ mcmd' = [mcmd EXCEPT ![self] = m.cmd]
                   /\ msgs' = (msgs \cup {([type |-> "2b", bal |-> m.bal, acc |-> self,
                                             cmd |-> m.cmd])})
           /\ pc' = [pc EXCEPT ![self] = "A"]
           /\ UNCHANGED << ldrBal, ldrPhs, learned >>

Acc(self) == A(self)

N(self) == /\ pc[self] = "N"
           /\ \E b \in Ballot:
                LET 2bMsgs == {m \in msgs : (m.type = "2b") /\ (m.bal = b)} IN
                  /\ {m.acc : m \in 2bMsgs} \in Majority
                  /\ \E m \in 2bMsgs:
                       learned' = [learned EXCEPT ![self] = m.cmd]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << msgs, ldrBal, ldrPhs, bal, mbal, mcmd >>

Lrn(self) == N(self)

Next == (\E self \in Leader: Ldr(self))
           \/ (\E self \in Acceptor: Acc(self))
           \/ (\E self \in Learner: Lrn(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

TypeOK == /\ msgs \subseteq Message
          /\ learned \in [Learner -> Command \cup {NotACmd}]
          /\ ldrBal  \in [Leader -> Ballot \cup {-1}]
          /\ ldrPhs  \in [Leader -> {1, 2}]
          /\ bal     \in [Acceptor -> Ballot \cup {-1}]
          /\ mbal    \in [Acceptor -> Ballot \cup {-1}]
          /\ mcmd    \in [Acceptor -> Command \cup {NotACmd}]
\*          /\ \A b \in Ballot :
\*               Cardinality({m \in msgs : (m.type = "1b") /\ (m.bal = b)})
\*                  < 2

Safety == \A l1, l2 \in Learner : 
             \/ learned[l2] = NotACmd
             \/ learned[l1] \in {learned[l2], NotACmd}

CONSTANTS MaxBallot, a1, a2, a3, ldr1, ldr2, lrn1, lrn2, cmd1, cmd2

MCAcceptor == {a1, a2, a3} \*  {a1} 
MCLeader   == {ldr1}
MCLearner  == {lrn1, lrn2} \*  {lrn1} 
MCLeaderOf == [i \in Ballot |-> ldr1]
MCCommand  == {cmd1, cmd2}
MCMajority == {{a1, a3}, {a1, a2}, {a2, a3}} \*  {{a1}} 

MCBallot   == 0..MaxBallot
=============================================================================
With
   MaxBallot = 2
   MCAcceptor == {a1, a2, a3}
   MCLeader   == {ldr1}
   MCLearner  == {lrn1, lrn2}
   MCLeaderOf == [i \in Ballot |-> ldr1]
   MCCommand  == {cmd1, cmd2}
   MCMajority == {{a1, a3}, {a1, a2}, {a2, a3}}

592889 distinct states found in Paxos and PcalPaxos

