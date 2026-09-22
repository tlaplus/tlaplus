-------------------------- MODULE DiskStateQueue ---------------------------
EXTENDS Integers, FiniteSets

\* Model switch, not a Java runtime configuration option.
CONSTANT SpuriousWakeups    \* Allow spurious Object.wait() returns.

CONSTANTS Threads,         \* Java thread identities (names in traces).
          Workers,         \* Cardinality models TLCGlobals.getNumWorkers().
          Capacity,        \* DiskStateQueue.BufSize: entries per buffer/pool.
          Writer,          \* Identity of the StatePoolWriter thread.
          Reader,          \* Identity of the StatePoolReader thread.
          Cleaner,         \* Identity of the StatePoolCleaner thread.
          RestoreQueue     \* Checkpoint occupancies/pool indices for recover().

None == "-"
Clients == Threads \ { Writer, Reader, Cleaner }
Monitors == { "q", "w", "r", "mu" }
EmptyQueue == [ enq |-> 0, deq |-> 0, lo |-> 1, hi |-> 0 ]
Size(q) == q.enq + q.deq + Capacity * ( q.hi - q.lo + 1 )

QueueType == [enq:0 .. Capacity, deq:0 .. Capacity, lo:Nat \ { 0 }, hi:Nat ]

\* A recording may omit background threads and may contain no workers.
ASSUME ThreadAssumption == /\ IsFiniteSet(Threads)
                           /\ Workers \subseteq Clients
                           /\ Cardinality({ Writer, Reader, Cleaner }) = 3
                           /\ None \notin
                                Threads \cup { Writer, Reader, Cleaner }
ASSUME CapacityAssumption == Capacity \in Nat \ { 0 }
ASSUME SwitchAssumption == SpuriousWakeups \in BOOLEAN
ASSUME RestoreAssumption == /\ RestoreQueue \in QueueType
                            /\ RestoreQueue.lo <= RestoreQueue.hi + 1

ControlLocations ==
  { "idle",
    "new",
    "call",
    "unsafeEnd",
    "announce",
    "announced",
    "waitQ",
    "offerEnter",
    "offer",
    "offerFlushed",
    "offered",
    "awaitEnter",
    "await",
    "waitW",
    "fillReady",
    "takeEnter",
    "take",
    "filled",
    "filledReturn",
    "run",
    "wait",
    "exit",
    "exited",
    "published",
    "finish",
    "finishMu",
    "finishEnd",
    "finishWriter",
    "finishReader",
    "finishReaderEnd",
    "finishCleaner",
    "suspend",
    "barrier",
    "barrierDone",
    "barrierMu",
    "waitMu",
    "recheck",
    "checkpoint",
    "commit",
    "recovered"
  }
Operations == { "none", "put", "get", "peek", "unsafePut" }
Kinds ==
  { "none",
    "load",
    "cache",
    "loadDone",
    "cacheHit",
    "cacheMiss",
    "finished",
    "wait",
    "done"
  }

\* Values and physical arrays are abstracted to occupancies. File numbers are
\* retained: [deleted, disk) is the interval of successfully written pool files.
\* A monitor is retained across nested calls and released by wait(), including
\* when its owner retains another monitor (notably q while waiting on w).
VARIABLES queue,
          balance,
          disk,
          deleted,
          writer,
          reader,
          cleaner,
          finish,
          stop,
          counted,
          owner,
          waiters,
          pc,
          op,
          kind,
          result,
          snapshot,
          checkpointTo
vars ==
  << queue,
     balance,
     disk,
     deleted,
     writer,
     reader,
     cleaner,
     finish,
     stop,
     counted,
     owner,
     waiters,
     pc,
     op,
     kind,
     result,
     snapshot,
     checkpointTo
  >>

\* Type and range predicate for every variable, including thread-local state.
TypeOK ==
  /\ queue \in QueueType /\ queue.lo <= queue.hi + 1
  /\ balance \in Nat
  /\ disk \in 0 .. queue.hi /\ deleted \in 0 .. ( queue.lo - 1 )
  /\ writer \in [file:{ -1 } \cup ( 0 .. queue.hi ), done:BOOLEAN ]
  /\ reader \in
       [file:{ -1 } \cup ( 0 .. queue.lo ),
         cache:{ -1 } \cup ( 0 .. queue.lo ),
         canRead:BOOLEAN,
         done:BOOLEAN
       ]
  /\ cleaner \in [done:BOOLEAN, limit:Nat, ready:BOOLEAN ]
  /\ finish \in BOOLEAN /\ stop \in BOOLEAN
  /\ counted \subseteq Workers
  /\ owner \in [Monitors -> Threads \cup { None }]
  /\ waiters \in [Monitors -> SUBSET Threads]
  /\ pc \in [Threads -> ControlLocations]
  /\ op \in [Threads -> Operations]
  /\ kind \in [Threads -> Kinds]
  /\ result \in [Threads -> BOOLEAN]
  /\ snapshot \in QueueType /\ snapshot.lo <= snapshot.hi + 1
  /\ checkpointTo \in Nat

Init ==
  /\ queue = EmptyQueue /\ balance = 0 /\ disk = 0 /\ deleted = 0
  /\ writer = [ file |-> -1, done |-> FALSE ]
  /\ reader = [ file |-> 0, cache |-> -1, canRead |-> FALSE, done |-> FALSE ]
  /\ cleaner = [ done |-> FALSE, limit |-> 0, ready |-> FALSE ]
  /\ finish = FALSE /\ stop = FALSE /\ counted = {}
  /\ owner = [m \in Monitors |-> None]
  /\ waiters = [m \in Monitors |-> {}]
  /\ pc = [p \in Threads |-> IF p \in { Writer, Reader } THEN "new" ELSE "idle"]
  /\ op = [p \in Threads |-> "none"] /\ kind = [p \in Threads |-> "none"]
  /\ result = [p \in Threads |-> FALSE]
  /\ snapshot = EmptyQueue /\ checkpointTo = 0

Free(m) == owner[m] = None
Own(p, m) == owner[m] = p
CanAcquire(p, m) == owner[m] \in { None, p }
CanWake(p, m) == Free(m) /\ p \notin waiters[m]
Signals(m) ==
  IF waiters[m] = {} THEN { {} } ELSE {waiters[m] \ { p }: p \in waiters[m]}
NeedWorkers == Cardinality(counted) < Cardinality(Workers)
CanUse(p) == Own(p, "q") /\ pc[p] \in { "call", "filledReturn" }

Call(p, operation) ==
  /\ p \in Clients /\ pc[p] = "idle" /\ Free("q")
  /\ operation \in { "put", "get", "peek" }
  /\ ( owner' = [owner EXCEPT !["q"] = p] /\ pc' = [pc EXCEPT ![p] = "call"] /\
             op' = [op EXCEPT ![p] = operation] /\
           result' = [result EXCEPT ![p] = FALSE] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            waiters,
            kind,
            snapshot,
            checkpointTo
         >>
     )

Return(p) ==
  /\ CanUse(p) /\ ( op[p] = "put" \/ result[p] )
  /\ ( owner' = [owner EXCEPT !["q"] = None] /\ pc' = [pc EXCEPT ![p] = "idle"] /\
           op' = [op EXCEPT ![p] = "none"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            waiters,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

AppendEntry(p) ==
  /\ queue.enq < Capacity
  /\ \/ /\ CanUse(p) /\ op[p] = "put"
        /\ ( queue' = [queue EXCEPT !.enq = @ + 1] /\ balance' = balance + 1 /\
                 result' = [result EXCEPT ![p] = TRUE] /\
               UNCHANGED << disk,
                  deleted,
                  writer,
                  reader,
                  cleaner,
                  finish,
                  stop,
                  counted,
                  owner,
                  waiters,
                  pc,
                  op,
                  kind,
                  snapshot,
                  checkpointTo
               >>
           )
     \/ /\ p \in Clients \ Workers /\ pc[p] = "idle" /\ Free("q")
        \* The non-synchronized API requires an exclusive caller (initialization).
        /\ ( queue' = [queue EXCEPT !.enq = @ + 1] /\ balance' = balance + 1 /\
                 pc' = [pc EXCEPT ![p] = "unsafeEnd"] /\
               UNCHANGED << disk,
                  deleted,
                  writer,
                  reader,
                  cleaner,
                  finish,
                  stop,
                  counted,
                  owner,
                  waiters,
                  op,
                  kind,
                  result,
                  snapshot,
                  checkpointTo
               >>
           )

Remove(p, peek) ==
  /\ CanUse(p) /\ op[p] = IF peek THEN "peek" ELSE "get"
  /\ ~finish /\ ~stop /\ queue.deq > 0
  /\ ( queue' = [queue EXCEPT !.deq = @ - IF peek THEN 0 ELSE 1] /\
               balance' = balance - ( IF peek THEN 0 ELSE 1 ) /\
             pc' = [pc EXCEPT ![p] = "call"] /\
           result' = [result EXCEPT ![p] = TRUE] /\
         UNCHANGED << disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            owner,
            waiters,
            op,
            kind,
            snapshot,
            checkpointTo
         >>
     )

EmptyReturn(p, finished) ==
  /\ CanUse(p) /\ op[p] \in { "get", "peek" }
  /\ IF finished
     THEN finish
     ELSE ~finish /\ Size(queue) = 0 /\
         Cardinality(counted) + 1 >= Cardinality(Workers)
  /\ ( result' = [result EXCEPT ![p] = TRUE] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            owner,
            waiters,
            pc,
            op,
            kind,
            snapshot,
            checkpointTo
         >>
     )

CanCountLast(p) ==
  /\ CanUse(p) /\ p \in Workers /\ op[p] \in { "get", "peek" }
  /\ ~finish /\ stop /\ Size(queue) > 0 /\ p \notin counted
  /\ Cardinality(counted) + 1 = Cardinality(Workers)

\* Counting the last worker precedes its acquisition of mu. This
\* boundary matters when the checkpointer holds mu and rechecks the barrier.
CountLast(p) ==
  /\ CanCountLast(p)
  /\ ( counted' = counted \cup { p } /\ pc' = [pc EXCEPT ![p] = "announce"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            owner,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

AnnounceLast(p) ==
  /\ pc[p] = "announce" /\ Own(p, "q") /\ Free("mu")
  /\ \E remaining \in Signals("mu"):
       ( waiters' = [waiters EXCEPT !["mu"] = remaining] /\
             pc' = [pc EXCEPT ![p] = "announced"] /\
           UNCHANGED << queue,
              balance,
              disk,
              deleted,
              writer,
              reader,
              cleaner,
              finish,
              stop,
              counted,
              owner,
              op,
              kind,
              result,
              snapshot,
              checkpointTo
           >>
       )

WaitWorker(p) ==
  /\ Own(p, "q") /\ p \in Workers
  /\ \/ pc[p] = "announced"
     \/ /\ pc[p] = "call" /\ ~finish /\ ( stop \/ Size(queue) = 0 )
        /\ Cardinality(counted) + 1 < Cardinality(Workers)
  /\ ( owner' = [owner EXCEPT !["q"] = None] /\
               waiters' = [waiters EXCEPT !["q"] = @ \cup { p }] /\
             counted' = counted \cup { p } /\
           pc' = [pc EXCEPT ![p] = "waitQ"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

WakeWorker(p) ==
  /\ pc[p] = "waitQ" /\ CanWake(p, "q")
  /\ ( owner' = [owner EXCEPT !["q"] = p] /\
               waiters' = [waiters EXCEPT !["q"] = @ \ { p }] /\
             counted' = counted \ { p } /\
           pc' = [pc EXCEPT ![p] = "call"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

NotifyWorkers(p) ==
  /\ CanUse(p) /\ op[p] = "put" /\ counted # {} /\ ~stop
  /\ ( waiters' = [waiters EXCEPT !["q"] = {}] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            owner,
            pc,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

\* Buffer handoff. Writing an older pending pool is synchronous under w and q.
StartOffer(p) ==
  /\ queue.enq = Capacity
  /\ ( ( CanUse(p) /\ op[p] = "put" ) \/
         ( p \in Clients \ Workers /\ pc[p] = "idle" /\ Free("q") )
     )
  /\ ( pc' = [pc EXCEPT ![p] = "offerEnter"] /\
           op' = [op EXCEPT ![p] = IF Own(p, "q") THEN "put" ELSE "unsafePut"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            owner,
            waiters,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

EnterWriter(p, offer) ==
  /\ pc[p] = IF offer THEN "offerEnter" ELSE "awaitEnter"
  /\ Free("w")
  /\ ( owner' = [owner EXCEPT !["w"] = p] /\
           pc' = [pc EXCEPT ![p] = IF offer THEN "offer" ELSE "await"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

FlushOld(p) ==
  /\ Own(p, "w") /\ pc[p] = "offer" /\ writer.file = disk
  /\ ( disk' = disk + 1 /\ pc' = [pc EXCEPT ![p] = "offerFlushed"] /\
         UNCHANGED << queue,
            balance,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            owner,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

Offer(p) ==
  /\ Own(p, "w") /\ pc[p] \in { "offer", "offerFlushed" }
  /\ writer.file = -1 \/ pc[p] = "offerFlushed"
  /\ \E remaining \in Signals("w"):
       ( writer' = [writer EXCEPT !.file = queue.hi] /\
                   queue' = [queue EXCEPT !.hi = @ + 1, !.enq = 0] /\
                 owner' = [owner EXCEPT !["w"] = None] /\
               waiters' = [waiters EXCEPT !["w"] = remaining] /\
             pc' = [pc EXCEPT ![p] = "offered"] /\
           UNCHANGED << balance,
              disk,
              deleted,
              reader,
              cleaner,
              finish,
              stop,
              counted,
              op,
              kind,
              result,
              snapshot,
              checkpointTo
           >>
       )

StartAwait(p) ==
  /\ CanUse(p) /\ op[p] \in { "get", "peek" } /\ queue.deq = 0
  /\ ~finish /\ ~stop /\ Size(queue) > 0 /\ queue.lo + 1 >= queue.hi
  /\ ( pc' = [pc EXCEPT ![p] = "awaitEnter"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            owner,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

WaitWriter(p) ==
  /\ Own(p, "w") /\ pc[p] = "await" /\ writer.file # -1
  /\ ( owner' = [owner EXCEPT !["w"] = None] /\
             waiters' = [waiters EXCEPT !["w"] = @ \cup { p }] /\
           pc' = [pc EXCEPT ![p] = "waitW"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

WakeWriterCaller(p) ==
  /\ pc[p] = "waitW" /\ CanWake(p, "w")
  /\ ( owner' = [owner EXCEPT !["w"] = p] /\
             waiters' = [waiters EXCEPT !["w"] = @ \ { p }] /\
           pc' = [pc EXCEPT ![p] = "await"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

AwaitDone(p) ==
  /\ Own(p, "w") /\ pc[p] = "await" /\ writer.file = -1
  /\ ( owner' = [owner EXCEPT !["w"] = None] /\
           pc' = [pc EXCEPT ![p] = "fillReady"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

StartTake(p, sourceKind) ==
  /\ Own(p, "q") /\ op[p] \in { "get", "peek" } /\ queue.deq = 0
  /\ ~finish /\ ~stop /\ Size(queue) > 0
  /\ IF sourceKind = "load"
     THEN /\ queue.lo + 1 <= queue.hi
          /\ pc[p] = "fillReady" \/
               ( pc[p] = "call" /\ queue.lo + 1 < queue.hi )
     ELSE pc[p] = "fillReady" /\ queue.lo + 1 > queue.hi
  /\ ( pc' = [pc EXCEPT ![p] = "takeEnter"] /\
           kind' = [kind EXCEPT ![p] = sourceKind] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            owner,
            waiters,
            op,
            result,
            snapshot,
            checkpointTo
         >>
     )

EnterReader(p) ==
  /\ pc[p] = "takeEnter" /\ Free("r")
  /\ ( owner' = [owner EXCEPT !["r"] = p] /\ pc' = [pc EXCEPT ![p] = "take"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

Take(p, source) ==
  /\ Own(p, "r") /\ pc[p] = "take"
  /\ CASE source = "cache" -> reader.cache # -1
     [] source = "file" ->
     reader.cache = -1 /\ reader.file # -1 /\
         ( kind[p] = "load" \/ reader.canRead ) /\
       reader.file \in deleted .. ( disk - 1 )
     [] source = "direct" ->
     kind[p] = "load" /\ reader.cache = -1 /\ reader.file = -1 /\
       queue.lo \in deleted .. ( disk - 1 )
     [] source = "empty" ->
     kind[p] = "cache" /\ reader.cache = -1 /\
       ( reader.file = -1 \/ ~reader.canRead )
  /\ LET full == source # "empty"
         exchange == source \in { "cache", "file" }
     IN ( queue' =
                         [queue EXCEPT
                         !.deq =
                         IF full THEN Capacity ELSE queue.enq,
                         !.enq =
                         IF full THEN @ ELSE 0,
                         !.lo =
                         @ + IF full THEN 1 ELSE 0] /\
                       reader' =
                         [reader EXCEPT
                         !.cache =
                         IF exchange THEN -1 ELSE @,
                         !.file =
                         IF exchange THEN queue.lo ELSE @,
                         !.canRead =
                         IF exchange THEN kind[p] = "load" ELSE @] /\
                     waiters' =
                       [waiters EXCEPT
                       !["r"] =
                       IF exchange /\ kind[p] = "load" THEN {} ELSE @] /\
                   owner' = [owner EXCEPT !["r"] = None] /\
                 pc' = [pc EXCEPT ![p] = "filled"] /\
               kind' =
                 [kind EXCEPT
                 ![p] =
                 IF kind[p] = "load"
                 THEN "loadDone"
                 ELSE IF full THEN "cacheHit" ELSE "cacheMiss"] /\
             UNCHANGED << balance,
                disk,
                deleted,
                writer,
                cleaner,
                finish,
                stop,
                counted,
                op,
                result,
                snapshot,
                checkpointTo
             >>
         )

\* Background processes retain their monitor between work and the next wait.
Boot(p, m) ==
  /\ pc[p] = "new" /\ Free(m)
  /\ ( pc' = [pc EXCEPT ![p] = "run"] /\ owner' = [owner EXCEPT ![m] = p] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

BackgroundWait(p, m) ==
  /\ Own(p, m) /\ pc[p] = "run"
  /\ IF p = Writer
     THEN writer.file = -1 /\ ~writer.done
     ELSE reader.file = -1 \/ reader.cache # -1 \/ ~reader.canRead
  /\ ( owner' = [owner EXCEPT ![m] = None] /\
             waiters' = [waiters EXCEPT ![m] = @ \cup { p }] /\
           pc' = [pc EXCEPT ![p] = "wait"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

BackgroundWake(p, m) ==
  /\ pc[p] = "wait" /\ CanWake(p, m)
  /\ ( owner' = [owner EXCEPT ![m] = p] /\
             waiters' = [waiters EXCEPT ![m] = @ \ { p }] /\
           pc' =
             [pc EXCEPT
             ![p] =
             IF p = Reader /\ reader.done THEN "exit" ELSE "run"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

Publish ==
  /\ Own(Writer, "w") /\ pc[Writer] = "run" /\ writer.file = disk
  /\ Free("r")
  \* Commit + nested reader notification are combined: w stays held, so no
  \* w waiter can observe the interval between them. Disk I/O is successful.
  /\ \E remaining \in Signals("w"):
       ( disk' = disk + 1 /\ writer' = [writer EXCEPT !.file = -1] /\
                 reader' = [reader EXCEPT !.canRead = TRUE] /\
               waiters' = [waiters EXCEPT !["w"] = remaining, !["r"] = {}] /\
             pc' = [pc EXCEPT ![Writer] = "published"] /\
           UNCHANGED << queue,
              balance,
              deleted,
              cleaner,
              finish,
              stop,
              counted,
              owner,
              op,
              kind,
              result,
              snapshot,
              checkpointTo
           >>
       )

Prefetch ==
  /\ Own(Reader, "r") /\ pc[Reader] = "run"
  /\ reader.cache = -1 /\ reader.canRead /\
       reader.file \in deleted .. ( disk - 1 )
  /\ ( reader' = [reader EXCEPT !.cache = reader.file, !.file = -1] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            cleaner,
            finish,
            stop,
            counted,
            owner,
            waiters,
            pc,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

BackgroundExit(p, m) ==
  /\ Own(p, m)
  /\ IF p = Writer
     THEN pc[p] = "run" /\ writer.done /\ writer.file = -1
     ELSE pc[p] = "exit" /\ reader.done
  /\ ( owner' = [owner EXCEPT ![m] = None] /\ pc' = [pc EXCEPT ![p] = "exited"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

\* Optional housekeeping is nondeterministically batched, rather than tied to
\* the implementation's 100-file threshold. It cannot delete an unconsumed pool.
RequestClean(p) ==
  /\ Own(p, "q") /\ pc[p] = "filledReturn"
  /\ ( cleaner' = [cleaner EXCEPT !.limit = queue.lo - 1, !.ready = TRUE] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            finish,
            stop,
            counted,
            owner,
            waiters,
            pc,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

Clean ==
  /\ ~cleaner.done /\ cleaner.ready
  /\ cleaner.limit <= queue.lo - 1
  /\ ( deleted' = cleaner.limit /\ cleaner' = [cleaner EXCEPT !.ready = FALSE] /\
         UNCHANGED << queue,
            balance,
            disk,
            writer,
            reader,
            finish,
            stop,
            counted,
            owner,
            waiters,
            pc,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

CleanerExit ==
  /\ cleaner.done /\ pc[Cleaner] # "exited"
  /\ ( pc' = [pc EXCEPT ![Cleaner] = "exited"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            owner,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

FinishBegin(p) ==
  /\ p \in Clients /\ pc[p] = "idle" /\ Free("q")
  /\ ( owner' = [owner EXCEPT !["q"] = p] /\ pc' = [pc EXCEPT ![p] = "finish"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

FinishSignal(p) ==
  /\ pc[p] = "finish" /\ Own(p, "q")
  /\ ( finish' = TRUE /\ waiters' = [waiters EXCEPT !["q"] = {}] /\
           pc' = [pc EXCEPT ![p] = "finishMu"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            stop,
            counted,
            owner,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

FinishNotify(p) ==
  /\ pc[p] = "finishMu" /\ Own(p, "q") /\ Free("mu")
  /\ \E remaining \in Signals("mu"):
       ( waiters' = [waiters EXCEPT !["mu"] = remaining] /\
             pc' = [pc EXCEPT ![p] = "finishEnd"] /\
           UNCHANGED << queue,
              balance,
              disk,
              deleted,
              writer,
              reader,
              cleaner,
              finish,
              stop,
              counted,
              owner,
              op,
              kind,
              result,
              snapshot,
              checkpointTo
           >>
       )

FinishQueue(p) ==
  /\ pc[p] = "finishEnd" /\ Own(p, "q")
  /\ ( owner' = [owner EXCEPT !["q"] = None] /\
           pc' = [pc EXCEPT ![p] = "finishWriter"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

FinishWriter(p) ==
  /\ pc[p] = "finishWriter" /\ Free("w")
  /\ ( writer' = [writer EXCEPT !.done = TRUE] /\
             waiters' = [waiters EXCEPT !["w"] = {}] /\
           pc' = [pc EXCEPT ![p] = "finishReader"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            owner,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

FinishReaderBegin(p) ==
  /\ pc[p] = "finishReader" /\ Free("r")
  /\ ( reader' = [reader EXCEPT !.done = TRUE] /\
             owner' = [owner EXCEPT !["r"] = p] /\
           pc' = [pc EXCEPT ![p] = "finishReaderEnd"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            cleaner,
            finish,
            stop,
            counted,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

FinishReader(p) ==
  /\ pc[p] = "finishReaderEnd" /\ Own(p, "r")
  /\ ( waiters' = [waiters EXCEPT !["r"] = {}] /\
             owner' = [owner EXCEPT !["r"] = None] /\
           pc' = [pc EXCEPT ![p] = "finishCleaner"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

FinishCleaner(p) ==
  /\ pc[p] = "finishCleaner"
  /\ ( cleaner' = [cleaner EXCEPT !.done = TRUE] /\
           pc' = [pc EXCEPT ![p] = "idle"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            finish,
            stop,
            counted,
            owner,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

SuspendBegin(p) ==
  /\ p \in Clients /\ pc[p] = "idle" /\ Free("q")
  /\ ( owner' = [owner EXCEPT !["q"] = p] /\ pc' = [pc EXCEPT ![p] = "suspend"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

StopWorkers(p) ==
  /\ pc[p] = "suspend" /\ Own(p, "q") /\ ~finish
  /\ ( stop' = TRUE /\ owner' = [owner EXCEPT !["q"] = None] /\
           pc' =
             [pc EXCEPT ![p] = IF NeedWorkers THEN "barrier" ELSE "barrierDone"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            counted,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

EnterBarrier(p) ==
  /\ pc[p] = "barrier" /\ Free("mu")
  \* Reads under mu can precede updates under q whose events are recorded before
  \* SuspendWait or SuspendEnd. Retain the values available on entry; the later
  \* actions can also observe subsequent updates. Acquiring mu and checking these
  \* fields are not one atomic operation with the eventual wait or return.
  /\ ( owner' = [owner EXCEPT !["mu"] = p] /\
             pc' = [pc EXCEPT ![p] = "barrierMu"] /\
           kind' =
             [kind EXCEPT
             ![p] =
             IF finish
             THEN "finished"
             ELSE IF NeedWorkers THEN "wait" ELSE "done"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            waiters,
            op,
            result,
            snapshot,
            checkpointTo
         >>
     )

WaitBarrier(p) ==
  /\ pc[p] = "barrierMu" /\ Own(p, "mu") /\ kind[p] # "finished"
  \* A worker can decrement and increment numWaiting while p holds mu. The
  \* condition read can precede that increment although the wait follows it.
  \* Abstract this interval while the worker's notification is still pending.
  /\ kind[p] = "wait" \/ NeedWorkers \/
       ( \E w \in Workers: pc[w] = "announce" )
  /\ ( owner' = [owner EXCEPT !["mu"] = None] /\
             waiters' = [waiters EXCEPT !["mu"] = @ \cup { p }] /\
           pc' = [pc EXCEPT ![p] = "waitMu"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

WakeBarrier(p) ==
  /\ pc[p] = "waitMu" /\ CanWake(p, "mu")
  \* The following unlogged monitor release is folded into the return from wait.
  /\ ( waiters' = [waiters EXCEPT !["mu"] = @ \ { p }] /\
           pc' = [pc EXCEPT ![p] = "recheck"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            owner,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

Recheck(p) ==
  /\ pc[p] = "recheck" /\ Free("q") /\ ~finish
  /\ ( pc' = [pc EXCEPT ![p] = IF NeedWorkers THEN "barrier" ELSE "barrierDone"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            owner,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

Suspended(p) ==
  /\ pc[p] = "barrierDone" \/
       /\ pc[p] = "barrierMu" /\ Own(p, "mu") /\ kind[p] # "finished"
       /\ kind[p] = "done" \/ ~NeedWorkers \/
            \* numWaiting is incremented before AvailCountLast is recorded.
            \* The read under mu can see that increment while the worker holds q.
            ( \E w \in Workers: CanCountLast(w)
            )
  /\ ( owner' = [owner EXCEPT !["mu"] = IF @ = p THEN None ELSE @] /\
           pc' = [pc EXCEPT ![p] = "idle"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

SuspendFinished(p, at) ==
  /\ finish
  /\ CASE at = "queue" -> pc[p] = "suspend" /\ Own(p, "q")
     [] at = "mu" -> pc[p] = "barrierMu" /\ Own(p, "mu")
     [] at = "recheck" -> pc[p] = "recheck" /\ Free("q")
  /\ ( owner' =
             [owner EXCEPT
             !["q"] =
             IF @ = p THEN None ELSE @,
             !["mu"] =
             IF @ = p THEN None ELSE @] /\
           pc' = [pc EXCEPT ![p] = "idle"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

Resume(p) ==
  \* ModelChecker resumes workers after beginChkpt, before commitChkpt.
  /\ p \in Clients /\ pc[p] \in { "idle", "commit" } /\ Free("q")
  /\ ( stop' = FALSE /\ waiters' = [waiters EXCEPT !["q"] = {}] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            counted,
            owner,
            pc,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

StartCheckpoint(p) ==
  /\ p \in Clients /\ pc[p] = "idle" /\ Free("q")
  /\ stop \/ finish
  \* Disabling/waking the cleaner happens BEFORE the logged snapshot completes.
  /\ ( cleaner' = [cleaner EXCEPT !.done = TRUE] /\
           pc' = [pc EXCEPT ![p] = "checkpoint"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            finish,
            stop,
            counted,
            owner,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

Snapshot(p) ==
  /\ pc[p] = "checkpoint"
  /\ ( snapshot' = queue /\ checkpointTo' = queue.lo - 1 /\
           pc' = [pc EXCEPT ![p] = "commit"] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            owner,
            waiters,
            op,
            kind,
            result
         >>
     )

Commit(p) ==
  /\ pc[p] = "commit"
  /\ ( deleted' = checkpointTo /\ pc' = [pc EXCEPT ![p] = "idle"] /\
         UNCHANGED << queue,
            balance,
            disk,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            owner,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

Restore(p) ==
  /\ p \in Clients /\ pc[p] = "idle" /\ Free("q") /\ Free("r")
  /\ queue = EmptyQueue /\ writer.file = -1 /\ ~finish
  /\ ( queue' = RestoreQueue /\ balance' = Size(RestoreQueue) /\
                   disk' = RestoreQueue.hi /\
                 deleted' = RestoreQueue.lo - 1 /\
               reader' =
                 [reader EXCEPT
                 !.file =
                 RestoreQueue.lo - 1,
                 !.cache =
                 -1,
                 !.canRead =
                 RestoreQueue.lo - 1 < RestoreQueue.hi] /\
             waiters' = [waiters EXCEPT !["r"] = {}] /\
           pc' = [pc EXCEPT ![p] = "recovered"] /\
         UNCHANGED << writer,
            cleaner,
            finish,
            stop,
            counted,
            owner,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

Advance(p, from, to) ==
  /\ pc[p] = from
  /\ ( pc' = [pc EXCEPT ![p] = to] /\
         UNCHANGED << queue,
            balance,
            disk,
            deleted,
            writer,
            reader,
            cleaner,
            finish,
            stop,
            counted,
            owner,
            waiters,
            op,
            kind,
            result,
            snapshot,
            checkpointTo
         >>
     )

\* Remove a thread from its wait set without notification. Monitor reacquisition
\* and return from wait are subsequent ordinary actions, not part of this step.
SpuriousWakeup(p) ==
  /\ SpuriousWakeups
  /\ \/ /\ \E m \in Monitors:
             /\ p \in waiters[m]
             /\ waiters' = [waiters EXCEPT ![m] = @ \ { p }]
        /\ UNCHANGED cleaner
     \* Cleaner waiting is abstracted by ready rather than a monitor wait set.
     \/ /\ p = Cleaner /\ ~cleaner.done /\ ~cleaner.ready
        /\ cleaner' = [cleaner EXCEPT !.ready = TRUE]
        /\ UNCHANGED waiters
  /\ UNCHANGED << queue, balance, disk, deleted, writer, reader, finish, stop,
                  counted, owner, pc, op, kind, result, snapshot, checkpointTo >>

\* Queue-action groups; workloads determine when clients invoke each operation.
EnqueueStep(p) ==
  \/ AppendEntry(p)
  \/ StartOffer(p)
  \/ EnterWriter(p, TRUE)
  \/ FlushOld(p)
  \/ Offer(p)
  \/ Advance(p, "offered", "call")

DequeueStep(p) ==
  \/ Remove(p, FALSE)
  \/ EmptyReturn(p, FALSE)
  \/ EmptyReturn(p, TRUE)
  \/ CountLast(p)
  \/ AnnounceLast(p)
  \/ WaitWorker(p)
  \/ WakeWorker(p)
  \/ StartAwait(p)
  \/ EnterWriter(p, FALSE)
  \/ WaitWriter(p)
  \/ WakeWriterCaller(p)
  \/ AwaitDone(p)
  \/ \E k \in { "load", "cache" }: StartTake(p, k)
  \/ EnterReader(p)
  \/ \E source \in { "cache", "file", "direct", "empty" }: Take(p, source)
  \/ Advance(p, "filled", "filledReturn")

SuspendStep(p) ==
  \/ StopWorkers(p)
  \/ EnterBarrier(p)
  \/ WaitBarrier(p)
  \/ WakeBarrier(p)
  \/ Recheck(p)
  \/ Suspended(p)
  \/ \E at \in { "queue", "mu", "recheck" }: SuspendFinished(p, at)

FinishStep(p) ==
  \/ FinishBegin(p)
  \/ FinishSignal(p)
  \/ FinishNotify(p)
  \/ FinishQueue(p)
  \/ FinishWriter(p)
  \/ FinishReaderBegin(p)
  \/ FinishReader(p)
  \/ FinishCleaner(p)

WriterStep ==
  \/ Boot(Writer, "w")
  \/ BackgroundWait(Writer, "w")
  \/ BackgroundWake(Writer, "w")
  \/ Publish
  \/ Advance(Writer, "published", "run")
  \/ BackgroundExit(Writer, "w")

ReaderStep ==
  \/ Boot(Reader, "r")
  \/ BackgroundWait(Reader, "r")
  \/ BackgroundWake(Reader, "r")
  \/ Prefetch
  \/ BackgroundExit(Reader, "r")

\* Conservation invariant: the enqueue/dequeue balance equals the
\* nonnegative abstract queue size.
Conservation == balance = Size(queue) /\ balance >= 0

DiskSafety ==
  \* At most one allocated pool remains unwritten.
  /\ queue.hi - disk \in 0 .. 1
  \* A cached pool is written and not deleted.
  /\ reader.cache # -1 => reader.cache \in deleted .. ( disk - 1 )
  \* A monitor's owner is not a member of its wait set.
  /\ \A m \in Monitors: owner[m] \notin waiters[m]

\* Conjunction of state predicates; []Safety is the safety property.
Safety == TypeOK /\ Conservation /\ DiskSafety

\* Thread p requires monitor m for its next control step. A notified
\* thread must reacquire its monitor; StatePoolWriter retains w while acquiring r.
RequiredMonitor(p, m) ==
  \* Enter a queue operation, return from wait, or recheck suspension.
  \/ /\ m = "q"
     /\ p \in Clients
     /\ pc[p] \in { "idle", "waitQ", "recheck" }
  \* Offer a pool, await writing, or request StatePoolWriter shutdown.
  \/ /\ m = "w"
     /\ pc[p] \in { "offerEnter", "awaitEnter", "waitW", "finishWriter" }
  \* Refill a buffer or request StatePoolReader shutdown.
  \/ /\ m = "r"
     /\ pc[p] \in { "takeEnter", "finishReader" }
  \* Signal or wait at the suspension barrier.
  \/ /\ m = "mu"
     /\ pc[p] \in { "announce", "finishMu", "barrier", "waitMu" }
  \* StatePoolWriter starts or reacquires its monitor after waiting.
  \/ /\ m = "w"
     /\ p = Writer
     /\ pc[p] \in { "new", "wait" }
  \* StatePoolReader starts or reacquires its monitor after waiting.
  \/ /\ m = "r"
     /\ p = Reader
     /\ pc[p] \in { "new", "wait" }
  \* Publish a pool and notify StatePoolReader while retaining w.
  \/ /\ m = "r"
     /\ p = Writer
     /\ pc[p] = "run"
     /\ writer.file # -1

\* Blocking on notification or monitor acquisition. Spurious wakeups are not
\* a source of progress. The cleaner's condition wait is represented by ready.
Blocked ==
  UNION { waiters[m]: m \in Monitors } \cup
    { p \in Threads:
      \/ \E m \in Monitors: RequiredMonitor(p, m) /\ ~CanAcquire(p, m)
      \/ p = Cleaner /\ ~cleaner.done /\ ~cleaner.ready }

ThreadLocal(p) == << pc[p], op[p], kind[p], result[p] >>

\* A step changes the local state of at most one thread. Monitor owners and
\* wait sets are shared state and are not subject to this locality property.
Locality ==
  [][\A p, q \in Threads:
    ( p # q /\ ThreadLocal(p)' # ThreadLocal(p) ) => UNCHANGED ThreadLocal(q)]_vars

\* The following liveness properties require client and fairness assumptions.
\* Every invoked suspension eventually returns, possibly because of shutdown.
SuspensionProgress ==
  \A p \in Clients: ( pc[p] = "suspend" ) ~> ( pc[p] = "idle" )

\* Every invoked shutdown eventually returns.
ShutdownProgress == \A p \in Clients: ( pc[p] = "finish" ) ~> ( pc[p] = "idle" )

\* A pending pool is eventually written, by the writer or an enqueue caller.
WriteProgress(f) == ( writer.file = f ) ~> ( disk > f )

\* A pending refill eventually returns to the dequeue caller.
ReadProgress ==
  \A p \in Clients:
    ( pc[p] \in { "awaitEnter", "takeEnter" } ) ~> ( pc[p] = "filledReturn" )
=============================================================================
