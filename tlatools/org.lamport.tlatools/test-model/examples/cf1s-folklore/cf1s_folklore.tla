------------------------------ MODULE cf1s_folklore ------------------------------

(* An encoding of the consensus algorithm with Byzantine faults in one communication step [1]. Here 
   we consider only the algorithm itself (Algorithm 2, lines 1--4), without looking at the underlying 
   consensus algorithm. 
   
   [1] Dobre, Dan, and Neeraj Suri. "One-step consensus with zero-degradation." Dependable Systems and 
   Networks, 2006. DSN 2006. International Conference on. IEEE, 2006.
                                                               
   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016
  
   This file is a subject to the license that is bundled together with this package and can be found 
   in the file LICENSE.
 *)


EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

VARIABLES nSnt0,    (* nSnt0, nSnt1 - the messages sent by correct processes *)
          nSnt1,
          nSnt0F,   (* nsnt0F, nsnt1F - the messages sent by faulty processes *)
          nSnt1F,  
          nFaulty,  (* the number of faulty processes *)
          pc,       (* process locations *)
          nRcvd0,   (* the number of received messages *)
          nRcvd1
          (* nStep - only for checking IndInv0 with TLC *)                

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
Status == { "V0", "V1", "S0", "S1", "D0", "D1", "U0", "U1", "BYZ" }
vars == << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, pc, nRcvd0, nRcvd1 >>


Init ==
  /\ pc \in [ Proc -> { "V0", "V1" } ]
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nSnt0F = 0
  /\ nSnt1F = 0
  /\ nFaulty = 0
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]
  
Faulty(i) ==
  /\ nFaulty < F
  /\ pc[i] # "BYZ"
  /\ pc' = [ pc EXCEPT ![i] = "BYZ" ] 
  /\ nFaulty' = nFaulty + 1  
  /\ IF pc[i] = "V0" THEN nSnt0F' = nSnt0F + 1 ELSE nSnt0F' = nSnt0F
  /\ IF pc[i] = "V1" THEN nSnt0F' = nSnt1F + 1 ELSE nSnt1F' = nSnt1F
  /\ UNCHANGED << nSnt0, nSnt1, nRcvd0, nRcvd1 >>
  
Propose(i) ==
  \/ /\ pc[i] = "V0"
     /\ pc' = [ pc EXCEPT ![i] = "S0" ]
     /\ nSnt0' = nSnt0 + 1
     /\ UNCHANGED << nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>
  \/ /\ pc[i] = "V1"
     /\ pc' = [ pc EXCEPT ![i] = "S1" ]
     /\ nSnt1' = nSnt1 + 1
     /\ UNCHANGED << nSnt0, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>
     
Receive(i) ==
  \/ /\ nRcvd0[i] < nSnt0 + nSnt0F
     /\ nRcvd0' = [ nRcvd0 EXCEPT ![i] = nRcvd0[i] + 1 ]
     /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nFaulty, pc, nSnt1F, nRcvd1 >>     
  \/ /\ nRcvd1[i] < nSnt1 + nSnt1F
     /\ nRcvd1' = [ nRcvd1 EXCEPT ![i] = nRcvd1[i] + 1 ]
     /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nFaulty, pc, nSnt1F, nRcvd0 >>    
  \/ /\ nRcvd0[i] = nSnt0
     /\ nRcvd1[i] = nSnt1
     /\ UNCHANGED vars 
     
Decide(i) ==
  /\ \/ pc[i] = "S0"
     \/ pc[i] = "S1"
  /\ nRcvd0[i] + nRcvd1[i] >= N - T
  /\ \/ /\ nRcvd0[i] >= N - T
        /\ pc' = [ pc EXCEPT ![i] = "D0" ]      
     \/ /\ nRcvd1[i] >= N - T
        /\ pc' = [ pc EXCEPT ![i] = "D1" ]
     \/ /\ nRcvd0[i] < N - T
        /\ nRcvd1[i] < N - T
        /\ pc[i] = "S0"
        /\ pc' = [ pc EXCEPT ![i] = "U0" ]
     \/ /\ nRcvd0[i] < N - T
        /\ nRcvd1[i] < N - T
        /\ pc[i] = "S1"
        /\ pc' = [ pc EXCEPT ![i] = "U1" ]
  /\ UNCHANGED << nSnt0, nSnt1, nSnt0F, nSnt1F, nFaulty, nRcvd0, nRcvd1 >>

Next ==
  /\ \E self \in Proc : 
        \/ Receive(self) 
        \/ Propose(self) 
        \/ Decide(self) 
        \/ Faulty(self)
        \/ UNCHANGED vars                  

(* Add weak fairness condition since we want to check liveness properties.  *)
(* We require that if UponV1 (UponNonFaulty, UponAcceptNotSent, UponAccept) *)
(* ever becomes forever enabled, then this step must eventually occur.      *)
Spec == Init /\ [][Next]_vars 
             /\ WF_vars(\E self \in Proc : \/ Receive(self)
                                           \/ Propose(self)
                                           \/ Decide(self))

(* All processes propose 0. *)
Init0 ==
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nSnt0F = 0
  /\ nSnt1F = 0
  /\ nFaulty = 0
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]
  (* /\ nStep = 0 *)
  
(* All processes propose 1. *)  
Init1 ==
  /\ pc = [ i \in Proc |-> "V1" ]
  /\ nSnt0 = 0
  /\ nSnt1 = 0
  /\ nSnt0F = 0
  /\ nSnt1F = 0
  /\ nFaulty = 0
  /\ nRcvd0 = [ i \in Proc |-> 0 ]
  /\ nRcvd1 = [ i \in Proc |-> 0 ]  


TypeOK == 
  /\ pc \in [ Proc -> Status ]          
  /\ nSnt0 \in 0..N
  /\ nSnt1 \in 0..N
  /\ nSnt0F \in 0..N
  /\ nSnt1F \in 0..N
  /\ nFaulty \in 0..F
  /\ nRcvd0 \in [ Proc -> 0..N ]
  /\ nRcvd1 \in [ Proc -> 0..N ]
  
 (* If all processes propose 0, then every process crashes or decides 0. *) 
OneStep0_Ltl ==
  (\A i \in Proc : pc[i] = "V0") => [](\A i \in Proc : pc[i] # "U0" /\ pc[i] # "U1" /\ pc[i] # "D1")

(* If all processes propose 1, then every process crashes or decides 1. *)
OneStep1_Ltl ==  
  (\A i \in Proc : pc[i] = "V1") => <>(\A i \in Proc : pc[i] # "U0" /\ pc[i] # "U1" /\ pc[i] # "D0")
 
StateConstraint ==
    TLCGet("level") < 6

=============================================================================
\* Modification History
\* Last modified Mon Jul 09 13:26:59 CEST 2018 by tthai
\* Created Mon Jun 04 13:20:35 CEST 2018 by tthai
