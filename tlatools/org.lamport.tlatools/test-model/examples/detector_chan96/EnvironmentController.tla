----------------------- MODULE EnvironmentController -----------------------

(* An encoding of a parameterized and partially synchronous model of the eventually  
   perfect failure detectors with crash faults from:
  
   [1] Chandra, Tushar Deepak, and Sam Toueg. "Unreliable failure detectors for 
   reliable distributed systems." Journal of the ACM (JACM) 43.2 (1996): 225-267.
        
   Igor Konnov, Thanh Hai Tran, Josef Wider, 2018
  
   This file is a subject to the license that is bundled together with this package 
   and can be found in the file LICENSE. *) 
   
(* - This specification instances two other specs, Age_Channel.tla for the communication 
     system, and EPFailureDetector.tla for behaviors of correct processes.
     
   - Every message sent by some process is wrapped into a box with an age which shows 
     how long this message have been in transit. Boxes for messages which were sent 
     but have not been delivered are stored in a variable inTransit.
     
   - Messages which are delivered in the current transition are stored in a variable
     inDelivery.
     
   - The system tracks what last transition a process takes, and how long some correct
     process has not taken a transition. The information are saved in variables moved
     and procPause, respectively. Crashes are also tracked.
     
   - Every process has its own local clock which is localClock[i].
    
   - Every correct process repeatedly sends "alive" messages to other processes, and 
     repeatedly make predictions about failures. However, a process cannot send and 
     predict at the same time. A process can receive messages when it does not execute 
     neither the operation SEND nor the operation PREDICT.
          
   - "alive" messages are created by calling the operator MakeAliveMsgsForAll in
     EPFailureDetector, and then stored in outgoingMessages.
       
   - In this specification, a correct process sends "alive" messages to others at every
     SendPoint tick of its local clock, and makes predictions about failures at every 
     PredictPoint tick of its local clock. Formally, we have that 
      a) localClock[i] % SendPoint = 0 /\ localClock[i] % PredictPoint # 0: a process
         executes the operation Send 
      b) localClock[i] % SendPoint # 0 /\ localClock[i] % PredictPoint = 0: a process
         executes the operation Predict
      c) \/ localClock[i] % SendPoint = 0 /\ localClock[i] % PredictPoint = 0
         \/ localClock[i] % SendPoint # 0 /\ localClock[i] % PredictPoint # 0 : a process
         executes the operation Receive
         
   - The predictions are saved in a variable suspected. If j \in suspected[i], a process
     p_i suspects that a process p_j crashed.
     
   - Every process p_i has a waiting time, called delta[i][j], for hearing some messages 
     for other process p_j. Moreover, a process tracks how long it hasn't receive any
     message from p_j, and stores the information in a variable fromLastHeard[i][j].
      
   - When a process p_i executes the action Predict, if p_i hasn't received any message
     from p_j for a too long period, e.g. fromLastHeard[i][j] > delta[i][j], p_i puts 
     p_j into its suspected list.
        
   o The keypoints in this specification is the way we encode the environmental clock,
     and local clocks of processes. This encoding technique makes our system become
     a finite one, if all parameters are fixed.
      
      1/ In this specification, instead of directly encoding the environmental clocks, 
      we focus on their effects on variables describing message delay, and relative 
      speeds of processes. The action EnvTick simulates an event of a global tick.
      When the action EnvTick is executed, a box with a message inside attains a 
      new age, and every pause of a process p_i, named procPause[i], is increased
      by 1.
    
      2/ Every local lock in this specification has a finite domain, instead of a
      infinite one. Whenever the value of its local clock is greater than SendPoint,
      PredictPoint, and delta[i][j], the local clock is reset to 0. Because of the 
      constraints about message delay and relative speeds of different processes in
      partial synchrony, the upper bound of local clocks exists.   
                                                                
      3/ After fromLastHeard[i][j] is greated than delta[i][j], we don't need to 
      increase fromLastHeard[i][j].                                                                           
  
   + We have used TLC to check the correctness of Strong Completeness and Eventually
     Strong Accuracy in small instances    
      - Strong Completeness: Eventually every process that crashes is permanently 
        suspected by every correct process. 
      - Eventually Strong Accuracy: There is a time after which correct processes 
        are not suspected by any correct process.
      - Case N = 3, T = 1, d0 = 2, SendPoint = 2, PredictPoint = 3, DELTA = PHI = 1:
        TLC spends more than 2 hours (from 11:17 to 13:26) verifying these properties.
      
   o PROBLEMS with TLC: I believe that PHIConstraint and PHIConstraint1 are equivalent. 
     However, whenever I check this specification with PHIConstraint1, TLC shows an 
     error: "Too many possible next states for the last state in the trace." I guess 
     that the reasons are from optimizations for disjunctions. *)   

EXTENDS Integers, TLC

CONSTANT 
  N,            (* The number of processes *)
  T,            (* The maximum number of failures *)
  d0,           (* The default time-out interval for all delta(p)(q) *)
  SendPoint,    (* Every correct process sends alive messages to others at every 
                   SendPoint ticks of its local clock. *)           
  PredictPoint, (* Every correct process makes predictions about failures at every 
                   PredictPoint ticks of its lock clock. 
                   Assume that SendPoint # PredictPoint since a process cannot both 
                   send alive messages and receive messages in one transition. *)
  DELTA,        (* For the constraint of message delay in partial synchrony. *)
  PHI           (* For the constraint of relative speeds of different processes in 
                   partial synchrony. *)
  
                        
(* Assumptions about the constraints in our system.
    - SendPoint # PredictPoint: a process cannot both send messages and 
      receive messages in one transition. 
    - PredictPoint % SendPoint # 0 /\ SendPoint % PredictPoint # 0 : 
      the operation Predict cannot subsume the operation Predict and vice versa. *)
ASSUME  /\ 0 < PredictPoint /\ 0 < SendPoint 
        /\ PredictPoint % SendPoint # 0 /\ SendPoint % PredictPoint # 0 
          
Proc == 1..N    (* A set of processes *)

VARIABLES 
  inTransit, inDelivery,            (* For the communication system: spec Age_Channel *)
  suspected, delta, fromLastHeard,  (* For correct detectors: spec EPFailureDetector *)      
  localClock, outgoingMessages, 
              (* For the environment: the current spec EnvironmentController. *)  
  procPause,  (* How long a process p_i has not taken a transition. *)
  moved,      (* The last transition that a process p_i take. The initial values are
                 INIT. After every global tick, moved'[i] is assigned "NO" for every
                 process. "NO" here means that a process has not taken a transition.
                 After a process p_i makes a transition, moved'[i] is assigned the 
                 transition name which are SEND, RECEIVE, PREDICT, or CRASH. *)
  failed,     (* failed[i] = TRUE: a process p_i crashed. *)
  F           (* A number of current failures *)
  
(* A set of messages sent by correct processes *)  
Messages == [ from : Proc, to : Proc, type : { "alive" } ]

(* Whenever a message is picked up, the communication system puts this message into
   a box with an age. The age shows how long a message has been in transit. The field
   "content" points to a message. *)
Boxes == [ content : Messages, age : Int ]

(*  - maxAge is an estimated upper bound of how long a message in transit. In other 
      word, this constant should be a maximum age of above boxes.
    - maxDelta is also an estimated upper bound of delta[i][j] for all i and j. *)
K == ((SendPoint * PredictPoint * PHI) \div DELTA) + 1 
maxAge == K * (SendPoint * PredictPoint * PHI)
maxDelta == maxAge

  
CommChan == INSTANCE Age_Channel        (* The communication system *) 

Detector == INSTANCE EPFailureDetector  (* Failure detectors *)

(* All variables *)
vars == << inTransit, inDelivery,
           suspected, delta, fromLastHeard, localClock, outgoingMessages,
           procPause, moved, failed, F >>
           
(* Variables for the communication system *)           
chanVars == << inTransit, inDelivery >>

(* Variables for the specification EPFailureDetector which describes behaviors  of 
   correct processes, *)
procVars == << suspected, delta, fromLastHeard, localClock, outgoingMessages >>

(* Variables for the environment *)
envVars == << procPause, moved, failed, F >>             

(* All Names of processes' transitions *)
Actions == { "NO", "INIT", "SEND", "RECEIVE", "PREDICT", "CRASH" }

(* Initialization *)
Init ==
  /\ CommChan!Init
  /\ Detector!Init
  /\ procPause = [ i \in Proc |-> 0 ]   (* No pauses *)
  /\ moved = [ i \in Proc |-> "INIT" ]  (* Every process finishes the initialization. *)                                         
  /\ failed = [ i \in Proc |-> FALSE ]  (* No failures *)    
  /\ F = 0                              (* No failures *)
  
(* A process p_i crashes. *)  
Crash ==
  \E i \in Proc : 
      /\ failed[i] = FALSE
      /\ F < T
      /\ failed' = [ failed EXCEPT ![i] = TRUE ]  
      /\ F' = F + 1
      /\ moved' = [ moved EXCEPT ![i] = "CRASH" ]    (* Required by SomeLocallyTicked *)
      /\ procPause' = [ procPause EXCEPT ![i] = -1 ]
      /\ UNCHANGED chanVars
      /\ UNCHANGED procVars
      
(* At every global tick, at least one correct process makes a transition. *)          
SomeLocallyTicked ==
  \E p \in Proc : moved[p] # "CRASH" /\ moved[p] # "NO"             
                      
(* A new tick of the environmental clock.
    - 1st conj: The global clock cannot have a new tick if no correct process makes
                a transition in the last global tick.
    - 2st conj: Every box's age increases by 1. 
    - 3nd conj: Reset moved. No processes have not taken a transition in this tick.
    - 4rd conj: Every pause is increased by 1. If a correct process p_i makes a 
                transition later but still in this global tick, its procPause are 
                reset to 0. *)                      
EnvTick ==
  /\ SomeLocallyTicked
  /\ CommChan!AttainAge
  /\ moved' = [ i \in Proc |-> "NO" ]
  /\ procPause' = [ i \in Proc |-> IF failed[i] = FALSE 
                                   THEN procPause[i] + 1
                                   ELSE -1 ]
  /\ UNCHANGED << failed, F >>
  /\ UNCHANGED procVars      

(* Only messages sent to correct processes are picked up. *)  
OnlyMessagesForCorrectProcesses(msgs) ==  { m \in msgs : failed[m.to] = FALSE }          
    
(* 1st disj: Even a process crashed, the associated messages are delivered to it.
             If these messages are not removed from the communication system, the ages 
             of these messages will increase infinitely.    
   2nd disj: The behaviors of correct processes.
    - A process can take a transition if t doesn't take any transition in the current
      global tick.  
    - A process p_i can makes predictions about failures. 
    - A process p_i can send "alive" messages to all. First, p_i creates "alive" messages 
      for all, and put those messages to outgoingMessages[i]. Then, the communication 
      system picks up those messages. 
    - A process p_i can receive new messages. First, the environment nondeterministically 
      choose some messages and put those messages into inDelivery'. Then, a process p_i
      receive those messages. *)  
ProcTick ==
  \E i \in Proc : 
      \/ /\ failed[i] = TRUE       
                                     
         /\ UNCHANGED envVars
         /\ CommChan!Deliver(i)   (* Some messages are delivery to a process p_i. *) 
         /\ UNCHANGED procVars    (* However, p_i cannot receive those messages because
                                     p_i crashed before. *)  
      \/ /\ failed[i] = FALSE     
         /\ moved[i] = "NO"       
         /\ procPause' = [ procPause EXCEPT ![i] = 0 ]          (* Reset procPause'[i]*)
         /\ UNCHANGED << failed, F >>
         /\ \/ /\ moved' = [ moved EXCEPT ![i] = "PREDICT" ]    
               /\ Detector!Predict(i)
               /\ UNCHANGED chanVars            
            \/ /\ moved' = [ moved EXCEPT ![i] = "SEND" ]       
               /\ Detector!SendAlive(i)                         
               /\ CommChan!Pickup(OnlyMessagesForCorrectProcesses(outgoingMessages'[i]))                                                           
            \/ /\ moved' = [ moved EXCEPT ![i] = "RECEIVE" ]                                                                               
               /\ CommChan!Deliver(i)
               /\ Detector!Receive(i, inDelivery')                    

(* Two constraints PHIConstraint and DELTAConstraint are respectively restrictions on
   message delay and relative speeds of processes in partial synchronoy. We use these 
   constraints to filter out executions. Only executions satisfying these constraints
   are allowed in the computation model of partial synchrony.  
     - PHIConstraint: In any contiguous subinterval containing PHI real-time steps, 
       every correct processor must take at least one step. In this specification, 
       this constraint is violated if there is a correct process such that the associated
       procPause is greater then PHI.
     - DELTAConstraint: If message m is placed in p_j’s buffer by some Send(m, p_j)  
       at a time s_1, and if p_j executes a Receive(p_j) at a time s_2 such that
       s_2 >= s_1 + DELTA, then m must be delivered to pj at time s_2 or earlier.
       This restriction is captured by the 1st conjunction in DELTAConstranti. 
       However, this constraint doesn't mention anything about messages sent to crashed
       processes which cannot execute the operation Receive. In this specification,
       we assume that the maximum delay of messages sent to crashed processes are DELTA
       real-time steps. In other words, the maximum ages of associated boxes in transit 
       are DELTA. *)                                                                             
PHIConstraint ==
  \A i \in Proc : (failed'[i] = FALSE => procPause'[i] <= PHI)  (* No errors happen *)

(* I believe that PHIConstraint and PHIConstraint1 are equivalent. However, whenever I 
   check this specification with PHIConstraing1, TLC shows an error: "Too many possible 
   next states for the last state in the trace." I guess that the reasons are from 
   optimizations for disjunctions. *)  
PHIConstraint1 ==
  \A i \in Proc : (failed'[i] = TRUE \/ procPause'[i] <= PHI)   
  

                                                                                                                                                                         
DELTAConstraint ==
  \A i \in Proc : /\ ((failed'[i] = FALSE /\ moved'[i] = "RECEIVE") 
                          => ( \A m \in inTransit' : \/ m.content.to # i
                                                     \/ m.age <= DELTA ))
                                                     (*
                  /\ ((failed'[i] = TRUE) 
                          => ( \A m \in inTransit' : \/ m.content.to # i
                                                     \/ m.age <= DELTA ))
                                                     *)                                                                    

(* Next transition *)
Next ==
  /\ \/ Crash
     \/ EnvTick
     \/ ProcTick     
  /\ DELTAConstraint  
  /\ PHIConstraint
                       
(* The specification *)                                  
Spec == 
  /\ Init  
  /\ [][ Next ]_vars   
  /\ WF_vars( /\ \/ EnvTick
                 \/ ProcTick
              /\ DELTAConstraint 
              /\ PHIConstraint )

(* Type invariant *)              
TypeOK ==
  /\ CommChan!TypeOK
  /\ Detector!TypeOK       
  /\ procPause \in [ Proc -> { -1 } \cup 0..PHI ]
  /\ \A i \in Proc : failed[i] = TRUE <=> procPause[i] = -1 
  /\ failed \in [ Proc -> BOOLEAN ]
  /\ moved \in [ Proc -> Actions]
  /\ F \in 0..T      
  /\ \A i, j \in Proc : 0 <= delta[i][j] /\ delta[i][j] <= maxDelta
  /\ \A box \in inTransit : 0 <= box.age /\ box.age <= maxAge   
  /\ \A i, j \in Proc : fromLastHeard[i][j] <= maxAge
  
(*Two properties of an eventually perfect failure detector 
    - Strong Completeness: Eventually every process that crashes is permanently 
      suspected by every correct process. 
    - Eventually Strong Accuracy: There is a time after which correct processes 
      are not suspected by any correct process. *) 
StrongCompleteness ==   
  <>[] ( \A j \in Proc : failed[j] = TRUE => (\A i \in Proc : \/ failed[i] = TRUE 
                                                              \/ j \in suspected[i] ) )
                                                             
EventuallyStrongAccuracy ==     
  <>[] ( \A i, j \in Proc : (failed[i] = FALSE /\ failed[j] = FALSE)  
                                => j \notin suspected[i] )     

StateConstraint ==
   TLCGet("level") < 20
=============================================================================
\* Modification History
\* Last modified Tue Jun 12 17:49:08 CEST 2018 by tthai
\* Created Mon Jun 04 13:20:35 CEST 2018 by tthai
