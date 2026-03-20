------------------------- MODULE EPFailureDetector -------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
  Proc,
  d0,           (* The default time-out interval for all delta(p)(q) *)
  SendPoint,    (* Every correct process sends alive messages to others at every 
                   SendPoint ticks of its local clock. *)           
  PredictPoint, (* Every correct process makes predictions about failures at every 
                   PredictPoint ticks of its lock clock. *)
  Messages  
  
(* Assumptions about the constraints in our system.
    - SendPoint # PredictPoint: a process cannot both send messages and receive 
      messages in one transition. 
    - PredictPoint % SendPoint # 0 /\ SendPoint % PredictPoint # 0 : the operation 
      Predict cannot subsume the operation Predict and vice versa. *)
ASSUME  /\ 0 < PredictPoint /\ 0 < SendPoint 
        /\ PredictPoint % SendPoint # 0 /\ SendPoint % PredictPoint # 0 
        
(*  Variables' role:
      - localClock[i]         a discrete integer-numbered local clock of a process p_i
      - suspected[i]          predictions about failures of p_i
      - delta[i][j]           a time-out interval which p_i waits for hearing something 
                              from a process p_j    
      - mailbox[i]            messages which p_i has received in the current transition
      - outgoingMessages[i]   messages which p_i wants to send in the current transition                                        
    More information:
      1/ A process p_i make a transition at every tick of its local clock localClock[i].
      2/ At every tick of the global clock, at least one correct processes make a 
         transition.
      3/ Processes can change their predictions. 
      4/ Correct processes eventually make stable predictions.
      5/ Whenever p_i receives an "alive" message from p_j, p_i increases the time-out 
         interval of j, removes j from its suspended list suspected[i], and updates its 
         fromLastHeard[i][j]. *)    
VARIABLES suspected, delta, fromLastHeard, localClock, outgoingMessages
  
vars == << suspected, delta, fromLastHeard, localClock, outgoingMessages >>

NULL == -1

(*  Create an "alive" message for every processes  *)
MakeAliveMsgsForAll(snder) == { [ from |-> snder, to |-> rcver, type |-> "alive" ] : 
                                        rcver \in Proc }

(* The initial state of processes 
    - 1st conj: No process p_is predicted as a faulty one. 
    - 2nd conj: Set every default time-out interval with d0. 
    - 3rd conj: No processes have received any messages from others. 
    - 4th conj: Every local clock starts at 0.
    - 5th conj: No messages were sent. *)
Init ==  
  /\ suspected = [ i \in Proc |-> {} ]                        
  /\ delta = [ i \in Proc |-> [ j \in Proc |-> d0 ] ]         
  /\ fromLastHeard = [ i \in Proc |-> [ j \in Proc |-> 0 ] ]  
  /\ localClock = [ i \in Proc |-> 0 ]                                  
  /\ outgoingMessages = [ i \in Proc |-> {} ]                 
  
(*  - Whenever the value of its local clock is greater than SendPoint, PredictPoint, 
      and delta[i][j], the local clock is reset to 0. 
    - Because of the constraints about message delay and relative speeds of different
      processes in partial synchrony, the upper bound of local clocks exists.    *)  
LocallyTick(i) ==
  localClock' = [ localClock EXCEPT ![i] = 
                                IF /\ \A j \in Proc : delta[i][j] < localClock[i] 
                                   /\ SendPoint < localClock[i]
                                   /\ PredictPoint < localClock[i]     
                                THEN 0
                                ELSE localClock[i] + 1 ]  
                 
(*  - A process p_i sends an "alive" message to every process at every SendPoint ticks
      of its local clock.
    - p_i constructs an "alive" messages for every process by calling MakeAliveMsgs, 
      and put these messages in its outgoingMessages which will be picked up by the 
      environmental controller in the composition action.   
    - p_i does not know exactly how the communication system works. *)
SendAlive(i) ==    
  /\ localClock[i] % PredictPoint # 0
  /\ localClock[i] % SendPoint = 0
  /\ LocallyTick(i)
  /\ outgoingMessages' = [ outgoingMessages EXCEPT ![i] = MakeAliveMsgsForAll(i)]
  /\ fromLastHeard' = [ fromLastHeard EXCEPT ![i] = 
                              [ j \in Proc |-> IF fromLastHeard[i][j] <= delta[i][j]
                                               THEN fromLastHeard[i][j]  + 1
                                               ELSE fromLastHeard[i][j] ] ]                                                           
  /\ UNCHANGED << suspected, delta >>
                                                                                                                                                                                                             
(*  - incomingMessages: A process does not know exactly how messages are feed to it. 
    - 1nd conj: A process p_i can perform the operation Receive if and only if it do
                not execute 
      the operations Send and Predict.    
    - 2nd conj: Update the value of its local clock.
    - 3rd conj: Update fromLastHeard immediately after new messages are received.
                If p_i receives a messages from p_j, then fromLastHeard[i][j] is reset
                to 0. If p_i does not receive a messages from p_j, fromLastHeard[i][j] is
                increased by 1. However, if fromLastHeard[i][j] is already greater than
                delta[i][j], we keep fromLastHeard[i][j] unchanged.  
    - 4th conj: Increase the waiting time for processes from which a process p_i has 
                received messages.
    - 5th conj: Update its predictions. All processes from which a process p_i has 
                received some message in this transition are marked as correct ones. 
    - 6th conj: outgoingMessages is irrelevant in this transition. *)            
Receive(i, incomingMessages) ==
  /\ \/ /\ localClock[i] % PredictPoint = 0
        /\ localClock[i] % SendPoint = 0
     \/ /\ localClock[i] % PredictPoint # 0
        /\ localClock[i] % SendPoint # 0
  /\ LocallyTick(i)
  /\ fromLastHeard' = [ fromLastHeard EXCEPT ![i] = 
                              [ j \in Proc |-> IF \E m \in incomingMessages : m.from = j 
                                               THEN 0
                                               ELSE IF j \notin suspected[i]
                                                    THEN IF fromLastHeard[i][j] <= delta[i][j]
                                                         THEN fromLastHeard[i][j] + 1
                                                         ELSE fromLastHeard[i][j]  
                                                    ELSE fromLastHeard[i][j] ] ]                                                         
  /\ delta' = [ delta EXCEPT ![i] = [ j \in Proc |-> IF /\ j \in suspected[i]
                                                        /\ \E m \in incomingMessages : m.from = j
                                                     THEN delta[i][j] + 1
                                                     ELSE delta[i][j] ] ]  
  /\ suspected' = [ suspected EXCEPT ![i] = suspected[i] \ { j \in Proc : (\E msg \in incomingMessages : msg.from = j) } ]  
  /\ UNCHANGED outgoingMessages                                                                                                                                                        

(*  - A process p_i makes predictions at every PredictPoint ticks of its local clock, based on messages 
      which it has received until now.     
    - If a process p_i has not received any message from a process p_j after delta[i][j] time units,
      a process p_i predicts that a process p_j is faulty. 
    - 6h conjunciton: outgoingMessages is irrelevant in this transition.  *)                                                                 
Predict(i) ==    
  /\ localClock[i] % PredictPoint = 0
  /\ localClock[i] % SendPoint # 0
  /\ LocallyTick(i)
  /\ suspected' = [ suspected EXCEPT ![i] = suspected[i] \cup { j \in Proc : fromLastHeard[i][j] > delta[i][j] } ]
  /\ UNCHANGED outgoingMessages
  /\ fromLastHeard' = [ fromLastHeard EXCEPT ![i] = [ j \in Proc |-> IF fromLastHeard[i][j] <= delta[i][j]
                                                                     THEN fromLastHeard[i][j] + 1
                                                                     ELSE fromLastHeard[i][j] ] ]
  /\ UNCHANGED << delta >>
    
(* Type invariant *)    
TypeOK ==        
  /\ fromLastHeard \in [ Proc -> [ Proc -> Int ] ]
  /\ \A p, q \in Proc : fromLastHeard[p][q] \in Int
  /\ delta \in [ Proc -> [ Proc -> Int ] ]
  /\ suspected \in [ Proc -> SUBSET Proc ]  
  /\ outgoingMessages  \in [ Proc -> SUBSET Messages ]                                                                               

=============================================================================
\* Modification History
\* Last modified Mon Jun 11 17:27:19 CEST 2018 by tthai
\* Created Mon Jun 04 12:39:53 CEST 2018 by tthai
