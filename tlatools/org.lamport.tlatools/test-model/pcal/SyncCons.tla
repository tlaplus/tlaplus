--algorithm SyncCons
        variables clock = 0;
                  input \in Data;
          round = [i \in 1..N |-> 0];
          buffer= { };
          crashed = { };

\***** Macros for sending and receiving messages
       macro Send(i, j, msg)
       begin 
       buffer := buffer \cup
         {[from |->  i,
           to   |->  j,
           msg  |-> IF i \in crashed
                     THEN bot
                      ELSE msg]};
       end macro

       macro Receive(i, j, msg)
       begin 
       when [from |->  i,
             to   |->  j,
             msg  |-> msg] \in buffer;
       buffer := buffer 
                   \ {[from |->  i,
                       to   |->  j,
                       msg  |-> msg]};
       end macro

\***** Synchronous consensus protocol for crash failures
\***** A crashed process sends "bot" messages, which model timeouts
       process Participant \in 1..N
        variables output = bot;
                  procs = { };
                  value = IF self = 1
                            THEN input
                            ELSE bot;
          recd = { };
          begin
s1:         while round[self] < t + 1 do
              when round[self] = clock;
              procs := 1..N;
s2:           while procs # { } do
                with dest \in procs do
                  Send(self, dest, value);
                  procs := procs \ {dest};
                  end with
                end while;
s3:           if self \notin crashed then
                procs := 1..N;
                recd := { };
s4:             while procs # { } do
                  with source \in Proc do
                    with data \in Data \cup {bot} do
                      Receive(source, self, data);
                      recd := recd \cup {data};
                      procs := procs \ {source};
                      end with
                    end with
                  end while;
s5:             if recd \cap Data = { }
                   then value := bot;
                   else value := CHOOSE i \in Data:
                                   i \in recd \cap Data;
                   end if;
                end if;
s6:           round[self] := round[self] + 1;
              end while;
            output := IF value = bot
                         THEN 0
                         ELSE value;  
            end process;
              
\***** Model of clock: ticks when all processes finish the current round
       process Clock = N + 1
         begin
clock:     while clock < t + 1 do
             when \A i \in 1..N: round[i] = clock + 1;
             clock := clock + 1;
             end while;
           end process;

\***** Crashing processes
       process Crash = N + 2
         begin
crash:     while Cardinality(crashed) < t do
             with x  \in (1..N) \ crashed do
               crashed  := crashed \cup {x}
               end with
             end while
           end process;

end algorithm

-------------------------------- MODULE SyncCons --------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, t, Data

ASSUME N > t

bot == CHOOSE v: v \notin Data

Proc == 1..N

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-6c62906a7a71f4a60f9b9f0eecf7e59e
\* Label clock of process Clock at line 77 col 12 changed to clock_
VARIABLES clock, input, round, buffer, crashed, pc, output, procs, value, 
          recd

vars == << clock, input, round, buffer, crashed, pc, output, procs, value, 
           recd >>

ProcSet == (1..N) \cup {N + 1} \cup {N + 2}

Init == (* Global variables *)
        /\ clock = 0
        /\ input \in Data
        /\ round = [i \in 1..N |-> 0]
        /\ buffer = { }
        /\ crashed = { }
        (* Process Participant *)
        /\ output = [self \in 1..N |-> bot]
        /\ procs = [self \in 1..N |-> { }]
        /\ value = [self \in 1..N |-> IF self = 1
                                        THEN input
                                        ELSE bot]
        /\ recd = [self \in 1..N |-> { }]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..N -> "s1"
                                        [] self = N + 1 -> "clock_"
                                        [] self = N + 2 -> "crash"]

s1(self) == /\ pc[self] = "s1"
            /\ IF round[self] < t + 1
                  THEN /\ round[self] = clock
                       /\ procs' = [procs EXCEPT ![self] = 1..N]
                       /\ pc' = [pc EXCEPT ![self] = "s2"]
                       /\ UNCHANGED output
                  ELSE /\ output' = [output EXCEPT ![self] = IF value[self] = bot
                                                                THEN 0
                                                                ELSE value[self]]
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ procs' = procs
            /\ UNCHANGED << clock, input, round, buffer, crashed, value, recd >>

s2(self) == /\ pc[self] = "s2"
            /\ IF procs[self] # { }
                  THEN /\ \E dest \in procs[self]:
                            /\ buffer' = (        buffer \cup
                                          {[from |->  self,
                                            to   |->  dest,
                                            msg  |-> IF self \in crashed
                                                      THEN bot
                                                       ELSE value[self]]})
                            /\ procs' = [procs EXCEPT ![self] = procs[self] \ {dest}]
                       /\ pc' = [pc EXCEPT ![self] = "s2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "s3"]
                       /\ UNCHANGED << buffer, procs >>
            /\ UNCHANGED << clock, input, round, crashed, output, value, recd >>

s3(self) == /\ pc[self] = "s3"
            /\ IF self \notin crashed
                  THEN /\ procs' = [procs EXCEPT ![self] = 1..N]
                       /\ recd' = [recd EXCEPT ![self] = { }]
                       /\ pc' = [pc EXCEPT ![self] = "s4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "s6"]
                       /\ UNCHANGED << procs, recd >>
            /\ UNCHANGED << clock, input, round, buffer, crashed, output, 
                            value >>

s4(self) == /\ pc[self] = "s4"
            /\ IF procs[self] # { }
                  THEN /\ \E source \in Proc:
                            \E data \in Data \cup {bot}:
                              /\ [from |->  source,
                                  to   |->  self,
                                  msg  |-> data] \in buffer
                              /\ buffer' = buffer
                                             \ {[from |->  source,
                                                 to   |->  self,
                                                 msg  |-> data]}
                              /\ recd' = [recd EXCEPT ![self] = recd[self] \cup {data}]
                              /\ procs' = [procs EXCEPT ![self] = procs[self] \ {source}]
                       /\ pc' = [pc EXCEPT ![self] = "s4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "s5"]
                       /\ UNCHANGED << buffer, procs, recd >>
            /\ UNCHANGED << clock, input, round, crashed, output, value >>

s5(self) == /\ pc[self] = "s5"
            /\ IF recd[self] \cap Data = { }
                  THEN /\ value' = [value EXCEPT ![self] = bot]
                  ELSE /\ value' = [value EXCEPT ![self] = CHOOSE i \in Data:
                                                             i \in recd[self] \cap Data]
            /\ pc' = [pc EXCEPT ![self] = "s6"]
            /\ UNCHANGED << clock, input, round, buffer, crashed, output, 
                            procs, recd >>

s6(self) == /\ pc[self] = "s6"
            /\ round' = [round EXCEPT ![self] = round[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << clock, input, buffer, crashed, output, procs, 
                            value, recd >>

Participant(self) == s1(self) \/ s2(self) \/ s3(self) \/ s4(self)
                        \/ s5(self) \/ s6(self)

clock_ == /\ pc[N + 1] = "clock_"
          /\ IF clock < t + 1
                THEN /\ \A i \in 1..N: round[i] = clock + 1
                     /\ clock' = clock + 1
                     /\ pc' = [pc EXCEPT ![N + 1] = "clock_"]
                ELSE /\ pc' = [pc EXCEPT ![N + 1] = "Done"]
                     /\ clock' = clock
          /\ UNCHANGED << input, round, buffer, crashed, output, procs, value, 
                          recd >>

Clock == clock_

crash == /\ pc[N + 2] = "crash"
         /\ IF Cardinality(crashed) < t
               THEN /\ \E x \in (1..N) \ crashed:
                         crashed' = (crashed \cup {x})
                    /\ pc' = [pc EXCEPT ![N + 2] = "crash"]
               ELSE /\ pc' = [pc EXCEPT ![N + 2] = "Done"]
                    /\ UNCHANGED crashed
         /\ UNCHANGED << clock, input, round, buffer, output, procs, value, 
                         recd >>

Crash == crash

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Clock \/ Crash
           \/ (\E self \in 1..N: Participant(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-166884a9c4ec2ab81b93439149dfdc07

C1 == \A p1, p2 \in (1..N) \ crashed:
  (pc[p1] = "Done" /\ pc[p2] = "Done") => (output[p1] = output[p2])

C2 == \A p \in (1..N) \ crashed:
  ( /\ 1 \notin crashed
    /\ pc[1] = "Done"
    /\ pc[p] = "Done" ) => (output[p] = input)

THEOREM Spec => [] C1 /\ [] C2
=================================================================================
On derosa.ucsd.edu (dual processor G5)
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
    calculated (optimistic):  8.312778857584233E-8
    based on the actual fingerprints:  8.652893187423173E-9
3093758 states generated, 619842 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 81.
181.963u 2.589s 2:47.51 110.1%  0+0k 2+119io 0pf+0w

