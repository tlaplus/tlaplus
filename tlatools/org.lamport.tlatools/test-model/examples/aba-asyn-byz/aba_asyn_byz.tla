------------------------------ MODULE aba_asyn_byz ------------------------------

(* An encoding of the asynchronous Byzantine consensus protocol in Fig.3 [1]: 

   [1] Bracha, Gabriel, and Sam Toueg. "Asynchronous consensus and broadcast protocols." 
   Journal of the ACM (JACM) 32.4 (1985): 824-840.
    
   Thanh Hai Tran, Igor Konnov, Josef Widder, 2016
 
   This file is a subject to the license that is bundled together with this package and can 
   be found in the file LICENSE.
 *)

EXTENDS Naturals (*, FiniteSets *), TLC

CONSTANTS N, T, F

VARIABLES nSntE,    (* the number of ECHO, READY messages which are sent      *)
          nSntR,    
          nRcvdE,   (* the number of ECHO, READY messages which are received  *)
          nRcvdR,  
          nByz,     (* the number of Byzantine processes                      *)
          pc        (* program counters *)
                          

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
Location == { "V0", "V1", "EC", "RD", "AC", "BYZ" }
vars == << nSntE, nSntR, nRcvdE, nRcvdR, nByz, pc >>
guardE == (N + T + 2) \div 2
guardR1 == T + 1
guardR2 == 2 * T + 1

(* Some processes propose 0 and others propose 1.*)
Init ==  
  /\ nSntE = 0                      (* Neither ECHO nor READY messages are sent.      *)
  /\ nSntR = 0    
  /\ nRcvdE = [ i \in Proc |-> 0 ]  (* Neither ECHO nor READY messages are received.  *)
  /\ nRcvdR = [ i \in Proc |-> 0 ]
  /\ nByz = 0                       (* No processes are faulty.                       *)
  /\ pc \in [ Proc -> { "V0", "V1" } ]
  
(* All processes propose 0. *)  
Init0 ==  
  /\ nSntE = 0
  /\ nSntR = 0    
  /\ nRcvdE = [ i \in Proc |-> 0 ]
  /\ nRcvdR = [ i \in Proc |-> 0 ]
  /\ nByz = 0
  /\ pc \in [ i \in Proc |-> "V0" ]  
  
(* All processes propose 1. *)  
Init1 ==  
  /\ nSntE = 0
  /\ nSntR = 0    
  /\ nRcvdE = [ i \in Proc |-> 0 ]
  /\ nRcvdR = [ i \in Proc |-> 0 ]
  /\ nByz = 0
  /\ pc \in [ i \in Proc |-> "V1" ]  
  
(* If there are less than F Byzantine processes, process i becomes faulty. *)
(* We requite i to be in an initial state (V0 or V1) to not break the      *)
(* message counting abstraction.                                           *)
BecomeByzantine(i) ==
  /\ nByz < F
  /\ \/ pc[i] = "V1"
     \/ pc[i] = "V0"
  /\ nByz' = nByz + 1  
  /\ pc' = [ pc EXCEPT ![i] = "BYZ" ]  
  /\ UNCHANGED << nSntE, nSntR, nRcvdE, nRcvdR >>

(* Process i receives a new message. If includeByz is TRUE, then messages from both   *)
(* correct and Byzantine processes are considered. Otherwise, only messages from      *)
(* correct processes are considered.                                                  *)
Receive(i, includeByz) ==
  \/ /\ nRcvdE[i] < nSntE + (IF includeByz THEN nByz ELSE 0)
     /\ nRcvdE' = [ nRcvdE EXCEPT ![i] = nRcvdE[i] + 1 ]
     /\ UNCHANGED << nSntE, nSntR, nRcvdR, nByz, pc >>     
  \/ /\ nRcvdR[i] < nSntR + (IF includeByz THEN nByz ELSE 0)
     /\ nRcvdR' = [ nRcvdR EXCEPT ![i] = nRcvdR[i] + 1 ]
     /\ UNCHANGED << nSntE, nSntR, nRcvdE, nByz, pc >>      
  \/ /\ UNCHANGED vars 

(* Process i will send an ECHO message if it proposed 1 and did not send an ECHO message. 
   If process i proposed 0, did not send an ECHO message but has received greater than 
   (N + F) / 2 ECHO messages or (F + 1) READY messages, it will also send an ECHO messages. 
 *)
SendEcho(i) ==
  /\ \/ pc[i] = "V1"
     \/ /\ pc[i] = "V0"
        /\ \/ nRcvdE[i] >= guardE
           \/ nRcvdR[i] >= guardR1
  /\ pc' = [ pc EXCEPT ![i] = "EC" ]
  /\ nSntE' = nSntE + 1
  /\ UNCHANGED << nSntR, nRcvdE, nRcvdR, nByz >>
  
(* If process i sent an ECHO message and has received enough ECHO or READY messages,
   it will send a READY messages.
 *)  
SendReady(i) ==
  /\ pc[i] = "EC" 
  /\ \/ nRcvdE[i] >= guardE
     \/ nRcvdR[i] >= guardR1
  /\ pc' = [ pc EXCEPT ![i] = "RD" ]
  /\ nSntR' = nSntR + 1
  /\ UNCHANGED << nSntE, nRcvdE, nRcvdR, nByz >>
     
(* If process has received READY messages from a majority of processes, it will accept. *)     
Decide(i) ==
  /\ pc[i] = "RD"     
  /\ nRcvdR[i] >= guardR2
  /\ pc' = [ pc EXCEPT ![i] = "AC" ]
  /\ UNCHANGED << nSntE, nSntE, nSntR, nRcvdE, nRcvdR, nByz >>

Next == 
  /\ \E self \in Proc : 
          \/ BecomeByzantine(self)
          \/ Receive(self, TRUE) 
          \/ SendEcho(self) 
          \/ SendReady(self)
          \/ Decide(self)    
          \/ UNCHANGED vars                

(* Add weak fairness condition since we want to check liveness properties.  *)
Spec == Init /\ [][Next]_vars 
             /\ WF_vars(\E self \in Proc : \/ Receive(self, FALSE)
                                           \/ SendEcho(self)
                                           \/ SendReady(self)
                                           \/ Decide(self))
                                           
Spec0 == Init0 /\ [][Next]_vars 
               /\ WF_vars(\E self \in Proc : \/ Receive(self, FALSE)
                                             \/ SendEcho(self)
                                             \/ SendReady(self)
                                             \/ Decide(self))                                           

TypeOK == 
  /\ pc \in [ Proc -> Location ]          
  /\ nSntE \in 0..N
  /\ nSntR \in 0..N
  /\ nByz \in 0..F
  /\ nRcvdE \in [ Proc -> 0..(nSntE + nByz) ]
  /\ nRcvdR \in [ Proc -> 0..(nSntR + nByz) ]
  
  
Unforg_Ltl ==
  (\A i \in Proc : pc[i] = "V0") => []( \A i \in Proc : pc[i] # "AC" )
  

Corr_Ltl == 
   (\A i \in Proc : pc[i] = "V1") => <>( \E i \in Proc : pc[i] = "AC" )
   
Agreement_Ltl ==
  []((\E i \in Proc : pc[i] = "AC") => <>(\A i \in Proc : pc[i] = "AC" \/ pc[i] = "BYZ" ))

StateConstraint ==
    TLCGet("level") < 8
  
=============================================================================
\* Modification History
\* Last modified Fri Jul 06 15:04:01 CEST 2018 by tthai

