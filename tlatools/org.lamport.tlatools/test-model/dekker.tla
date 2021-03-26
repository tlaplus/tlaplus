---- CONFIG dekker ----
SPECIFICATION
    Spec
PROPERTIES
    Termination 
CONSTANT
    Threads = {t1,t2,t3}
====
------------------------------- MODULE dekker -------------------------------
EXTENDS TLC, Integers
CONSTANT Threads

(*--algorithm dekker

variables 
  flag = [t \in Threads |-> FALSE],
  next_thread \in Threads;

define
  \* At most one thread is in the critical section at a time
  AtMostOneCritical == \A t1, t2 \in Threads:
    t1 /= t2 => ~(pc[t1] = "CS" /\ pc[t2] = "CS")
  
  \* All threads eventually reach the critical section
  Liveness == \A t \in Threads: <>(pc[t] = "CS")
end define;

fair process thread \in Threads
begin
  P1: flag[self] := TRUE;
  P2:
    while \E t \in Threads \ {self}: flag[t] do
      P2_1:
        if next_thread /= self then
          P2_1_1: flag[self] := FALSE;
          P2_1_2: await next_thread = self;
          P2_1_3: flag[self] := TRUE;
        end if;
    end while;
  CS: skip; \* CS means "critical section"
  P3: with t \in Threads \ {self} do
        next_thread := t;
      end with;
  P4: goto P1;
end process;

end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES flag, next_thread, pc

(* define statement *)
AtMostOneCritical == \A t1, t2 \in Threads:
  t1 /= t2 => ~(pc[t1] = "CS" /\ pc[t2] = "CS")


Liveness == \A t \in Threads: <>(pc[t] = "CS")


vars == << flag, next_thread, pc >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ flag = [t \in Threads |-> FALSE]
        /\ next_thread \in Threads
        /\ pc = [self \in ProcSet |-> "P1"]

P1(self) == /\ pc[self] = "P1"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED next_thread

P2(self) == /\ pc[self] = "P2"
            /\ IF \E t \in Threads \ {self}: flag[t]
                  THEN /\ pc' = [pc EXCEPT ![self] = "P2_1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "CS"]
            /\ UNCHANGED << flag, next_thread >>

P2_1(self) == /\ pc[self] = "P2_1"
              /\ IF next_thread /= self
                    THEN /\ pc' = [pc EXCEPT ![self] = "P2_1_1"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "P2"]
              /\ UNCHANGED << flag, next_thread >>

P2_1_1(self) == /\ pc[self] = "P2_1_1"
                /\ flag' = [flag EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "P2_1_2"]
                /\ UNCHANGED next_thread

P2_1_2(self) == /\ pc[self] = "P2_1_2"
                /\ next_thread = self
                /\ pc' = [pc EXCEPT ![self] = "P2_1_3"]
                /\ UNCHANGED << flag, next_thread >>

P2_1_3(self) == /\ pc[self] = "P2_1_3"
                /\ flag' = [flag EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "P2"]
                /\ UNCHANGED next_thread

CS(self) == /\ pc[self] = "CS"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "P3"]
            /\ UNCHANGED << flag, next_thread >>

P3(self) == /\ pc[self] = "P3"
            /\ \E t \in Threads \ {self}:
                 next_thread' = t
            /\ pc' = [pc EXCEPT ![self] = "P4"]
            /\ flag' = flag

P4(self) == /\ pc[self] = "P4"
            /\ pc' = [pc EXCEPT ![self] = "P1"]
            /\ UNCHANGED << flag, next_thread >>

thread(self) == P1(self) \/ P2(self) \/ P2_1(self) \/ P2_1_1(self)
                   \/ P2_1_2(self) \/ P2_1_3(self) \/ CS(self) \/ P3(self)
                   \/ P4(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(thread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Sun Sep 29 12:39:24 PDT 2019 by tony
\* Created Sun Sep 29 12:18:45 PDT 2019 by tony


