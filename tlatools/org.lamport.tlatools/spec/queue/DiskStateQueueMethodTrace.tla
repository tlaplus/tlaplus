-------------------- MODULE DiskStateQueueMethodTrace ----------------------
EXTENDS DiskStateQueue, QueueJpfData, TLC

\* Replays method, field, and monitor observations from DiskStateQueueJPFTest.
\* Every replay step consumes an observation. TLC checks that each recorded
\* execution prefix corresponds to a behavior prefix of DiskStateQueue.
ASSUME JpfNodeCount > 0

\* Retain suspendAll's result between monitor release and method return, and
\* relate isAvail's result to the subsequent sDequeue return value. Reader
\* branch observations determine the source consumed at the helper's return.
VARIABLES node, suspension, available, readSource

MethodInit ==
  /\ Init /\ node = 0
  /\ suspension = [p \in Clients |-> "idle"]
  /\ available = [p \in Clients |-> FALSE]
  /\ readSource = [p \in Clients |-> "none"]
  /\ TLCSet(0, { 0 })

MethodTypeOK ==
  /\ node \in 0 .. JpfNodeCount
  /\ suspension \in [Clients -> { "idle", "active", "true", "false" }]
  /\ available \in [Clients -> BOOLEAN]
  /\ readSource \in [Clients -> { "none", "cache", "file", "direct", "empty" }]

ReaderBranch(p, a) ==
  /\ pc[p] = "take" /\ Own(p, "r")
  /\ CASE a \in { "StatePoolReader.doWork.isFull.ifeq.false", "StatePoolReader.getCache.isFull.ifeq.false" } ->
     /\ reader.cache # -1
     /\ readSource' = [readSource EXCEPT ![p] = "cache"]
     [] a \in { "StatePoolReader.doWork.isFull.ifeq.true", "StatePoolReader.getCache.isFull.ifeq.true" } ->
     /\ reader.cache = -1
     /\ readSource' = [readSource EXCEPT ![p] = "none"]
     [] a \in { "StatePoolReader.doWork.poolFile.ifnull.true", "StatePoolReader.getCache.poolFile.ifnull.true" } ->
     /\ reader.file = -1
     \* A null check also occurs in the assertion on the cache branch.
     /\ readSource' = [readSource EXCEPT ![p] = IF @ = "cache" THEN @ ELSE IF kind[p] = "load" THEN "direct" ELSE "empty"]
     [] a \in { "StatePoolReader.doWork.poolFile.ifnull.false", "StatePoolReader.getCache.poolFile.ifnull.false" } ->
     /\ reader.file # -1 /\ readSource[p] = "none"
     /\ readSource' = [readSource EXCEPT ![p] = "file"]
     [] a = "StatePoolReader.getCache.canRead.ifeq.true" -> /\ ~reader.canRead /\ readSource[p] = "file"
                                                            /\ readSource' = [readSource EXCEPT ![p] = "empty"]
     [] a = "StatePoolReader.getCache.canRead.ifeq.false" -> /\ reader.canRead /\ readSource[p] = "file"
                                                             /\ UNCHANGED readSource
     [] OTHER-> FALSE
  /\ UNCHANGED << vars, suspension, available >>

ObserveMethod(p, a) ==
  \/ /\ CASE a = "StateQueue.sEnqueue.enter" -> Call(p, "put")
        [] a = "StateQueue.sDequeue.enter" -> Call(p, "get")
        [] a = "StateQueue.sEnqueue.return" -> op[p] = "put" /\ Return(p)
        [] a = "StateQueue.enqueue.return" -> Advance(p, "unsafeEnd", "idle")
        [] a = "DiskStateQueue.enqueueInner.return" -> AppendEntry(p)
        [] a = "StatePoolWriter.doWork.call" -> StartOffer(p)
        [] a = "StatePoolWriter.doWork.enter" -> EnterWriter(p, TRUE)
        [] a = "StatePoolWriter.doWork.flush" -> FlushOld(p)
        [] a = "StatePoolWriter.doWork.return.buffer" -> Offer(p)
        [] a = "DiskStateQueue.enqueueInner.spilled" -> Advance(p, "offered", IF op[p] = "unsafePut" THEN "idle" ELSE "call")
        [] a = "StatePoolWriter.ensureWritten.call" -> StartAwait(p)
        [] a = "StatePoolWriter.ensureWritten.lock" -> EnterWriter(p, FALSE)
        [] a = "StatePoolWriter.ensureWritten.unlock" -> AwaitDone(p)
        [] a = "StatePoolReader.doWork.call" -> StartTake(p, "load")
        [] a = "StatePoolReader.getCache.call" -> StartTake(p, "cache")
        [] a = "StatePoolReader.doWork.enter" -> kind[p] = "load" /\ EnterReader(p)
        [] a = "StatePoolReader.getCache.enter" -> kind[p] = "cache" /\ EnterReader(p)
        [] a = "DiskStateQueue.fillDeqBuffer.return" -> Advance(p, "filled", "filledReturn")
        [] a = "DiskStateQueue.dequeueInner.return.state" -> available[p] /\ Remove(p, FALSE)
        [] a = "StateQueue.sDequeue.return.state" -> op[p] = "get" /\ available[p] /\ Return(p)
        [] a = "StateQueue.sDequeue.return.null" -> op[p] = "get" /\ ~available[p] /\ Return(p)
        [] a = "StateQueue.finishAll.enter" -> FinishBegin(p)
        [] a = "StateQueue.finishAll.return" -> FinishQueue(p)
        [] a = "DiskStateQueue.finishAll.return" -> pc[p] = "idle" /\ cleaner.done /\ UNCHANGED vars
        [] a = "StateQueue.resumeAll.return" -> Resume(p)
        [] a = "StateQueue.isAvail.countLast" -> CountLast(p)
        [] a = "StateQueue.isAvail.notify.mu" -> AnnounceLast(p)
        [] a = "StateQueue.isAvail.wait" -> WaitWorker(p)
        [] a = "StateQueue.isAvail.wake" -> WakeWorker(p)
        [] a = "StateQueue.sEnqueue.notifyAll" -> NotifyWorkers(p)
        [] a = "StateQueue.suspendAll.lock.q" -> /\ suspension[p] = "active"
                                                 /\ SuspendBegin(p) \/ ( pc[p] = "recheck" /\ Free("q") /\ UNCHANGED vars )
        [] a \in { "StateQueue.suspendAll.unlock.q.wait", "StateQueue.suspendAll.unlock.q.done" } ->
        /\ StopWorkers(p) \/ Recheck(p)
        /\ pc'[p] = IF a = "StateQueue.suspendAll.unlock.q.wait" THEN "barrier" ELSE "barrierDone"
        [] a = "StateQueue.suspendAll.lock.mu" -> EnterBarrier(p)
        [] a = "StateQueue.suspendAll.unlock.mu" -> pc[p] = "recheck" /\ UNCHANGED vars
        [] a = "StateQueue.suspendAll.wait" -> WaitBarrier(p)
        [] a = "StateQueue.suspendAll.wake" -> WakeBarrier(p)
        [] a = "StatePoolWriter.ensureWritten.wait" -> WaitWriter(p)
        [] a = "StatePoolWriter.ensureWritten.wake" -> WakeWriterCaller(p)
        [] a = "StateQueue.finishAll.finish.true" -> FinishSignal(p)
        [] a = "StateQueue.finishAll.notify.mu" -> FinishNotify(p)
        [] a = "StatePoolWriter.setFinished.finished.true" -> FinishWriter(p)
        [] a = "StatePoolReader.setFinished.finished.true" -> FinishReaderBegin(p)
        [] a = "DiskStateQueue.finishAll.notifyAll.reader" -> FinishReader(p)
        [] a = "DiskStateQueue.finishAll.finished.true" -> FinishCleaner(p)
        [] a = "StatePoolWriter.run.lock" -> p = Writer /\ Boot(p, "w")
        [] a = "StatePoolWriter.run.wait" -> p = Writer /\ BackgroundWait(p, "w")
        [] a = "StatePoolWriter.run.wake" -> p = Writer /\ BackgroundWake(p, "w")
        [] a = "StatePoolWriter.run.unlock" -> p = Writer /\ BackgroundExit(p, "w")
        [] a = "StatePoolReader.wakeup.return" -> p = Writer /\ Publish
        [] a = "StatePoolWriter.run.repeat" -> p = Writer /\ Advance(p, "published", "run")
        [] a = "StatePoolReader.run.lock" -> p = Reader /\ Boot(p, "r")
        [] a = "StatePoolReader.run.wait" -> p = Reader /\ BackgroundWait(p, "r")
        [] a = "StatePoolReader.run.wake" -> p = Reader /\ BackgroundWake(p, "r")
        [] a = "StatePoolReader.run.unlock" -> p = Reader /\ BackgroundExit(p, "r")
        [] a = "StatePoolReader.run.isFull.true" -> p = Reader /\ Prefetch
        [] a = "DiskStateQueue$StatePoolCleaner.run.return" -> p = Cleaner /\ CleanerExit
        [] OTHER-> FALSE
     /\ UNCHANGED << suspension, available, readSource >>
  \/ ReaderBranch(p, a)
  \/ /\ a \in { "StatePoolReader.doWork.return.buffer", "StatePoolReader.getCache.return.buffer", "StatePoolReader.getCache.return.null" }
     /\ readSource[p] \in { "cache", "file", "direct", "empty" }
     /\ ( a = "StatePoolReader.getCache.return.null" ) = ( readSource[p] = "empty" )
     /\ Take(p, readSource[p])
     /\ readSource' = [readSource EXCEPT ![p] = "none"]
     /\ UNCHANGED << suspension, available >>
  \/ /\ a \in { "StateQueue.isAvail.return.true", "StateQueue.isAvail.return.false" }
     /\ IF a = "StateQueue.isAvail.return.true"
        THEN /\ CanUse(p) /\ op[p] = "get" /\ UNCHANGED vars
        ELSE \E f \in BOOLEAN: EmptyReturn(p, f)
     /\ available' = [available EXCEPT ![p] = ( a = "StateQueue.isAvail.return.true" )]
     /\ UNCHANGED << suspension, readSource >>
  \/ /\ a = "StateQueue.suspendAll.enter"
     /\ suspension[p] = "idle"
     /\ suspension' = [suspension EXCEPT ![p] = "active"]
     /\ UNCHANGED << vars, available, readSource >>
  \/ /\ a = "StateQueue.suspendAll.unlock.mu.return.true"
     /\ suspension[p] = "active" /\ Suspended(p)
     /\ suspension' = [suspension EXCEPT ![p] = "true"]
     /\ UNCHANGED << available, readSource >>
  \/ /\ a \in { "StateQueue.suspendAll.unlock.q.return.false", "StateQueue.suspendAll.unlock.mu.return.false" }
     /\ suspension[p] = "active"
     /\ SuspendFinished(p, IF a = "StateQueue.suspendAll.unlock.mu.return.false"
          THEN "mu"
          ELSE IF pc[p] = "suspend" THEN "queue" ELSE "recheck")
     /\ suspension' = [suspension EXCEPT ![p] = "false"]
     /\ UNCHANGED << available, readSource >>
  \/ /\ a \in { "StateQueue.suspendAll.return.true", "StateQueue.suspendAll.return.false" }
     /\ IF a = "StateQueue.suspendAll.return.true"
        THEN \/ suspension[p] = "true" /\ UNCHANGED vars
             \/ suspension[p] = "active" /\ pc[p] = "barrierDone" /\ Suspended(p)
        ELSE suspension[p] = "false" /\ UNCHANGED vars
     /\ suspension' = [suspension EXCEPT ![p] = "idle"]
     /\ UNCHANGED << available, readSource >>

MethodStep(child) ==
  /\ LET event == JpfEvent(child) IN ObserveMethod(event.thread, event.action)
  /\ node' = child

\* Compose an unobserved spurious wakeup with the recorded step, consuming it once.
MethodNext ==
  \E child \in JpfChildren(node):
    \/ MethodStep(child)
    \/ ( SpuriousWakeup(JpfEvent(child).thread) /\ UNCHANGED << node, suspension, available, readSource >> )
       \cdot MethodStep(child)

\* Trace validation requires a matching specification behavior prefix for every recorded execution prefix,
\* including prefixes whose exploration terminates at a previously visited JPF state.
\* RememberNodes accumulates reachable trace-tree nodes in worker-local TLC storage, outside the specification state.
\* AllNodesReplayed is the acceptance postcondition. Run TLC with one worker to accumulate the complete set.
RememberNodes == TLCSet(0, TLCGet(0) \cup { node })
AllNodesReplayed == TLCGet(0) = 0 .. JpfNodeCount
=============================================================================
