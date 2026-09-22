----------------------- MODULE DiskStateQueueWorkload -----------------------
EXTENDS DiskStateQueue

\* Independent of recorded traces. The main thread enqueues Capacity + 1 initial
\* states before workers start, then suspends, checkpoints, and resumes them.
\* A worker dequeues once, nondeterministically enqueues any number of entries
\* if successful, and calls finishAll when its enqueue batch returns.
\* Thus a worker blocked by suspension cannot simply abandon its operation.
\* Recovery, repeated checkpoints, peeking, and cleaner requests are outside
\* this workload. No model-checking bounds restrict its actions.
CONSTANT Main

ASSUME WorkloadAssumption == /\ Main \in Clients \ Workers
                             /\ Clients = Workers \cup { Main }
                             /\ Workers # {}
                             /\ { Writer, Reader, Cleaner } \subseteq Threads

VARIABLE stage
workloadVars == << vars, stage >>

WorkloadTypeOK ==
  /\ stage \in
       [Clients
       ->
       { "initialStates",
         "suspend",
         "suspending",
         "checkpoint",
         "resume",
         "get",
         "got",
         "empty",
         "put",
         "append",
         "putReturn",
         "finish",
         "done"
       }]

WorkloadInit ==
  /\ Init
  /\ stage = [p \in Clients |-> IF p = Main THEN "initialStates" ELSE "get"]

\* Once notification occurs, the batch can only return, not append more entries.
PutReturn(p) ==
  \/ /\ ~stop /\ waiters["q"] # {} /\ NotifyWorkers(p)
     /\ stage' = [stage EXCEPT ![p] = "putReturn"]
  \/ /\ stop \/ waiters["q"] = {}
     /\ Return(p)
     /\ stage' = [stage EXCEPT ![p] = IF p = Main THEN "suspend" ELSE "finish"]

\* Complete an insertion, including any spill, before choosing to return.
BatchAppend(p) ==
  /\ EnqueueStep(p)
  /\ stage' =
       [stage EXCEPT
       ![p] =
       IF balance' > balance
       THEN IF p = Main THEN "initialStates" ELSE "put"
       ELSE "append"]

\* Workers choose whether to append or finish; the initial-state batch is fixed.
PutStep(p) ==
  \/ /\ pc[p] = "idle" /\ Call(p, "put")
     /\ UNCHANGED stage
  \/ /\ pc[p] # "idle"
     /\ p \in Workers \/ Size(queue) < Capacity + 1
     /\ BatchAppend(p)
  \/ /\ p \in Workers \/ Size(queue) = Capacity + 1
     /\ PutReturn(p)

MainStep ==
  LET p == Main
  IN \/ /\ stage[p] = "initialStates" /\ PutStep(p)
     \/ /\ stage[p] = "append" /\ BatchAppend(p)
     \/ /\ stage[p] = "putReturn" /\ PutReturn(p)
     \/ /\ stage[p] = "suspend"
        /\ SuspendBegin(p)
        /\ stage' = [stage EXCEPT ![p] = "suspending"]
     \/ /\ stage[p] = "suspending"
        /\ SuspendStep(p)
        /\ stage' = [stage EXCEPT ![p] = IF pc'[p] # "idle" THEN @ ELSE IF finish THEN "done" ELSE "checkpoint"]
     \/ /\ stage[p] = "checkpoint"
        /\ StartCheckpoint(p) \/ Snapshot(p) \/ Commit(p)
        /\ stage' = [stage EXCEPT ![p] = IF pc'[p] = "idle" THEN "resume" ELSE @]
     \/ /\ stage[p] = "resume"
        /\ Resume(p)
        /\ stage' = [stage EXCEPT ![p] = "done"]

WorkerStep(p) ==
  /\ stage[Main] \notin { "initialStates", "append", "putReturn" }
  /\ \/ /\ stage[p] = "get"
        /\ Call(p, "get") \/ DequeueStep(p)
        /\ stage' = [stage EXCEPT ![p] = IF balance' < balance THEN "got" ELSE IF result'[p] THEN "empty" ELSE @]
     \/ /\ stage[p] \in { "got", "empty" }
        /\ Return(p)
        /\ stage' = [stage EXCEPT ![p] = IF @ = "got" THEN "put" ELSE "finish"]
     \/ /\ stage[p] = "put" /\ PutStep(p)
     \/ /\ stage[p] = "append" /\ BatchAppend(p)
     \/ /\ stage[p] = "putReturn" /\ PutReturn(p)
     \/ /\ stage[p] = "finish"
        /\ FinishStep(p)
        /\ stage' = [stage EXCEPT ![p] = IF pc'[p] = "idle" THEN "done" ELSE @]

BackgroundStep(p) ==
  /\ \/ /\ p = Writer /\ WriterStep
     \/ /\ p = Reader /\ ReaderStep
     \/ /\ p = Cleaner /\ ( Clean \/ CleanerExit )
  /\ UNCHANGED stage

Next ==
  \/ MainStep
  \/ \E p \in Workers: WorkerStep(p)
  \/ \E p \in { Writer, Reader, Cleaner }: BackgroundStep(p)
  \/ /\ \E p \in Threads: SpuriousWakeup(p)
     /\ UNCHANGED stage

Spec == WorkloadInit /\ [][Next]_workloadVars

\* Clients must return and the writer must complete shutdown. The reader and
\* cleaner need not terminate for the workload to finish.
Terminated == /\ \A p \in Clients: stage[p] = "done"
              /\ pc[Writer] = "exited"

\* Exclude terminated threads and workers not yet started by the main thread.
ActiveThreads ==
  { p \in Threads:
    /\ pc[p] # "exited"
    /\ p \in Clients => stage[p] # "done"
    \* Main's initial batch, including pending append/return steps, must finish
    \* before workers start. This restricts Main's stage, not the workers' stages.
    /\ p \in Workers => stage[Main] \notin { "initialStates", "append", "putReturn" } }

\* Unless terminated, at least one active thread is not blocked. This state
\* predicate excludes spurious wakeups and does not assert eventual progress.
DeadlockFree == Terminated \/ ActiveThreads \ Blocked # {}
=============================================================================
