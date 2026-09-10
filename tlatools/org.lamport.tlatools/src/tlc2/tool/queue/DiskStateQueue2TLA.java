/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.tool.queue;

import jdk.jfr.Category;
import jdk.jfr.Description;
import jdk.jfr.Enabled;
import jdk.jfr.Event;
import jdk.jfr.Label;
import jdk.jfr.Name;
import jdk.jfr.StackTrace;

/**
 * Records execution traces of {@link DiskStateQueue} as JFR events for replay
 * against a TLA+ specification.
 * <p>
 * A {@link DiskStateQueue} is five kinds of process - the TLC workers, the pool
 * writer, the pool reader, the cleaner, and whoever stops them all to take a
 * checkpoint - meeting over four monitors at the points named by {@link Action}.
 * The order in which they meet, not anything the queue computes, is what decides
 * whether an execution is one the specification allows; GH issue 1403 is an
 * execution in which they met in an order nobody had considered.
 * <p>
 * An event therefore says which action a thread completed and nothing else: not
 * how full the buffers were, not which pool file, not which thread was woken.
 * Some of that a thread cannot honestly report - a Java monitor does not expose
 * its wait set, and the writer's fields are not the worker's to read - and the
 * rest the specification already computes. Because every process sits at a
 * control point that its last action determines, a sequence of (thread, action)
 * pairs pins the state down and TLC's non-determinism supplies the remainder -
 * among it the order of the few pairs that share a timestamp, which is an order
 * nothing in the execution fixed either.
 * <p>
 * The events are {@link Enabled}{@code (false)}: {@link Action#Enq} and
 * {@link Action#Deq} occur once per state and would swamp a recording taken for
 * any other purpose. Ask for them explicitly, and do not omit {@code maxsize=0},
 * because JFR may otherwise discard earlier events needed for replay.
 *
 * <pre>
 * java -XX:StartFlightRecording=dumponexit=true,maxsize=0,filename=queue.jfr,+tlc2.DiskStateQueue#enabled=true ...
 * </pre>
 *
 * A harness turns them on with {@code recording.enable(}{@link #EVENT_NAME}{@code )}.
 *
 * @see <a href="https://arxiv.org/abs/2404.16075">Validating Traces of
 *      Distributed Programs Against TLA+ Specifications</a>
 * @see <a href="https://github.com/lemmy/BlockingQueue">Weeks of debugging can
 *      save you hours of TLA+, v19 (Traces)</a>
 */
public final class DiskStateQueue2TLA {

	/** The JFR name of the event, as {@link jdk.jfr.Recording#enable(String)} wants it. */
	public static final String EVENT_NAME = "tlc2.DiskStateQueue";

	/**
	 * The points at which one thread of a {@link DiskStateQueue} becomes visible
	 * to another, each of which a specification models as a single action.
	 * <p>
	 * {@code X} is one atomic step. {@code XBegin}/{@code XEnd} bracket a stretch
	 * across which another thread may run and this one may be stuck - a monitor
	 * held, a blocking call outstanding, or both - so the two ends are two actions
	 * and not one; an {@code XBegin} that never reaches its {@code XEnd} is a
	 * thread that never got unstuck, which is what GH issue 1403 looks like from
	 * here. {@code XWait}/{@code XWoke} are the same for a stretch across which
	 * {@link Object#wait()} has <em>released</em> a monitor the thread holds on
	 * either side of it, which is where every lost wakeup in this subsystem lives.
	 * <p>
	 * Actions are grouped by the class that emits them and hence by the monitor
	 * that orders them. Those from {@link StateQueue} come from the abstract base
	 * class, so {@code MemStateQueue} and {@code DiskByteArrayQueue} emit them too
	 * but with no {@link #Enq} between {@link #SEnqueueBegin} and
	 * {@link #SEnqueueEnd}: a recording to validate the disk queue against has to
	 * come from a run that used one.
	 */
	public enum Action {

		// ---- DiskStateQueue: the buffers, the pool files and the cleaner -------

		Enq, // appended a state to enqBuf
		Deq, // removed one from deqBuf
		Peek, // read the head of deqBuf without removing it
		SpillBegin, // enqBuf is full, so it is being offered to the writer
		SpillEnd, // the writer took it; another pool file is on its way to disk
		AwaitWriteBegin, // waiting for the writer to have no pool file left
		AwaitWriteEnd,
		LoadPoolBegin, // asking the reader for the pool file that follows loPool
		LoadPoolEnd,
		TakeCacheBegin, // asking the reader for a pool file it has already read
		TakeCacheHit,
		TakeCacheMiss, // it had none, so enqBuf was drained into deqBuf instead
		NotifyCleaner, // asking the cleaner to delete the pool files below loPool
		Clean, // it did, and advanced lastLoPool
		BeginChkpt,
		CommitChkpt,
		Recover,
		FinishWriter,
		FinishReader,
		FinishCleaner,
		CleanerExit,
		Delete,

		// ---- StateQueue: the monitor the workers contend for -------------------

		Enqueue, // through the API that is not thread safe, so under no monitor
		Dequeue,
		DequeueEmpty,
		SEnqueueBegin, // holding the queue, about to add states to it
		SEnqueueNotify, // and waking the workers that were waiting for some
		SEnqueueEnd,
		SDequeueBegin,
		SDequeueEnd,
		SPeekBegin,
		SPeekEnd,
		AvailFinished, // asked for states, but the queue was already shut down
		AvailNoWork, // queue empty and all other workers waiting: the search is over
		AvailAllWaiting, // last to wait but queue not empty, so woke the checkpointer
		AvailWait, // gave up the queue to wait for a state
		AvailWoke,
		AvailWokeFinished, // and found the queue shut down
		FinishAllBegin,
		FinishAllNotifyMu, // the checkpointer must not wait for workers that are gone
		FinishAllEnd,
		SuspendBegin, // the checkpointer holds the queue and wants the workers to stop
		SuspendFinished, // but it is shut down, so there is nothing to suspend
		SuspendStop, // asked them to stop, released the queue to let them notice
		SuspendAwaitBegin, // holding the lock the last worker to stop will wake it on
		SuspendFinishedOnMu,
		SuspendWait, // gave up that lock to wait for the workers
		SuspendWoke,
		SuspendRecheck, // back on the queue, counting the workers still running
		SuspendFinishedOnRecheck,
		SuspendEnd, // all stopped, so the queue is the checkpointer's alone
		Resume,
		ResumeStuckMu, // a suspend nobody was going to end, unwedged by hand
		ResumeStuckQueue,

		// ---- StatePoolWriter: the thread that spills a buffer to disk ----------

		WriterDoWorkBegin, // a worker holds the writer and is handing it a buffer
		WriterDoWorkLate, // the writer never got to the last one, so the worker wrote it
		WriterDoWorkEnd,
		WriterAwaitBegin, // a worker holds the writer and wants nothing left outstanding
		WriterAwaitWait,
		WriterAwaitWoke,
		WriterAwaitEnd,
		WriterRunBegin, // the writer thread started and holds itself
		WriterWait, // nothing to write, so it gave up its monitor
		WriterWoke,
		WriterExit, // observed the finished flag with no buffer left to write
		WriterWrote, // wrote the file, woke the waiters, offered it to the reader
		WriterBeginChkpt, // unreachable: a checkpoint format TLC no longer uses
		WriterRecover, // unreachable, as WriterBeginChkpt

		// ---- StatePoolReader: the thread that reads the next buffer back -------

		ReaderWakeup, // the writer says a pool file is ready to be read
		ReaderRestart, // pointed at a different pool file after a recovery
		ReaderDoWorkBegin,
		ReaderDoWorkPrefetched, // the reader had it, so the worker took the buffer
		ReaderDoWorkPending, // it had not, so the worker read that file itself
		ReaderDoWorkDirect, // it had nothing to read, so the worker read its own file
		ReaderGetCacheBegin,
		ReaderGetCachePrefetched,
		ReaderGetCacheRead, // nothing prefetched, but a file was ready, so the worker read it
		ReaderGetCacheEmpty, // nothing at all
		ReaderRunBegin, // the reader thread started and holds itself
		ReaderWait,
		ReaderWoke,
		ReaderExit, // what woke it was the shutdown
		ReaderRead, // read a pool file into its buffer, which a worker may now take
		ReaderBeginChkpt, // unreachable, as WriterBeginChkpt
		ReaderRecover, // unreachable, as WriterBeginChkpt
		ReaderSetFinished
	}

	@Name(EVENT_NAME)
	@Label("DiskStateQueue Action")
	@Description("A thread of a DiskStateQueue completed one action of the queue's TLA+ specification.")
	@Category({ "TLA+", "Trace Validation" })
	@StackTrace(false)
	@Enabled(false)
	static final class ActionEvent extends Event {

		@Label("Action")
		String action;

		@Label("Sequence")
		@Description("Counts the actions of one thread, so that its own order survives a timestamp that ties.")
		long seq;
	}

	/**
	 * Orders the actions a thread took against each other. JFR's timestamps order
	 * the threads against one another well enough - on a 6M action recording not
	 * one pair of actions on the same monitor shared a timestamp, because a monitor
	 * handoff costs far more than the clock's resolution - but they are too coarse
	 * to separate a thread from itself: a tenth of all consecutive same-thread pairs
	 * tie. Those are program order, not concurrency, and this restores them. The
	 * counter is per thread and so contends with nothing; a shared one would order
	 * the concurrent actions too, which is an order the execution did not have.
	 * <p>
	 * Measured before it was written this way, the two behave alike: over 32 runs
	 * each, no statistic of the queue's races separates a shared {@code AtomicLong}
	 * from this (smallest p over some fifty of them, 0.06). What does separate them
	 * is recording at all, which lets the writer keep up more often than it would
	 * (p = 0.008) because a worker traces about six actions per state and the writer
	 * about five per pool file, so the recording taxes the two unequally. Worth
	 * remembering before adding an event to the workers' path.
	 */
	private static final ThreadLocal<long[]> SEQUENCE = ThreadLocal.withInitial(() -> new long[1]);

	/** The calling thread has just completed {@code action}. */
	public static void trace(final Action action) {
		final ActionEvent event = new ActionEvent();
		if (!event.isEnabled()) {
			// The JIT folds this away and scalar-replaces the event.
			return;
		}
		event.action = action.name();
		event.seq = ++SEQUENCE.get()[0];
		event.commit();
	}

	private DiskStateQueue2TLA() {
		// no instances
	}
}
