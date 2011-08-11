// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:27 PST by lamport
//      modified on Tue Feb 13 18:38:24 PST 2001 by yuanyu

package tlc2.tool.queue;

import java.io.IOException;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.TLCState;
import tlc2.tool.Worker;
import util.Assert;

public abstract class StateQueue {
	/**
	 * In model checking, this is the sequence of states waiting to be explored
	 * further. When the queue is empty, the checking is completed.
	 */
	protected int len = 0; // the queue length
	private int numWaiting = 0; // the number of waiting threads
	private boolean finish = false; // terminate
	/**
	 * Signals {@link Worker} that checkpointing is going happen next.
	 */
	private boolean stop = false; // suspend all workers.
	/**
	 * Synchronizes between workers and checkpointing. More precisely it is used
	 * to notify (wake up) the checkpointing thread once the last worker is
	 * done.
	 */
	private Object mu = new Object();

	/* Enqueues the state. It is not thread-safe. */
	public final void enqueue(final TLCState state) {
		this.enqueueInner(state);
		this.len++;
	}

	/**
	 * Returns the first element in the queue. It returns null if the queue is
	 * empty. It is not thread-safe.
	 */
	public final TLCState dequeue() {
		if (isEmpty()) {
			return null;
		}
		final TLCState state = this.dequeueInner();
		this.len--;
		return state;
	}

	/* Enqueues a state. Wake up any waiting thread. */
	public final synchronized void sEnqueue(final TLCState state) {
		this.enqueueInner(state);
		this.len++;
		if (this.numWaiting > 0 && !this.stop) {
			this.notifyAll();
		}
	}

	/* Enqueues a list of states. Wake up any waiting thread. */
	public final synchronized void sEnqueue(final TLCState states[]) {
		for (int i = 0; i < states.length; i++) {
			this.enqueueInner(states[i]);
		}
		this.len += states.length;
		if (this.numWaiting > 0 && !this.stop) {
			this.notifyAll();
		}
	}

	/* Return the first element in the queue. Wait if empty. */
	public final synchronized TLCState sDequeue() {
		if (this.isAvail()) {
			final TLCState state = this.dequeueInner();
			Assert.check(state != null, EC.GENERAL);
			this.len--;
			return state;
		}
		return null;
	}

	/**
	 * Return (up to) the first count elements in the queue. Wait if empty.
	 * 
	 * @param cnt
	 *            Amount of states requested
	 * @return null iff no states are available && all work is done @see
	 *         {@link #isAvail()}, states otherwise
	 * @throws RuntimeException
	 *             if cnt <= 0
	 */
	public final synchronized TLCState[] sDequeue(int cnt) {
		Assert.check(cnt > 0, EC.GENERAL);
		if (this.isAvail()) {
			if (cnt > len) {
				cnt = len;
			}
			final TLCState states[] = new TLCState[cnt];
			int idx;
			for (idx = 0; idx < cnt && this.len > 0; idx++) {
				states[idx] = this.dequeueInner();
				this.len--;
			}
			if (idx == cnt) {
				return states;
			}

			// cnt >= index, shrink resulting array
			// dead code due to resetting cnt == len if cnt > len
			final TLCState res[] = new TLCState[idx];
			for (int i = 0; i < idx; i++) {
				res[i] = states[i];
			}
			return res;
		}
		return null;
	}

	/**
	 * Checks if states are available. If no states are available, the callee
	 * will be put to sleep until new states are available or another callee
	 * signals work done. This is determined by the fact, that all other workers
	 * are waiting for states.
	 * 
	 * @return true if states are available in the queue.
	 */
	private final boolean isAvail() {
		if (this.finish) {
			return false;
		}
		while (isEmpty() || this.stop) {
			this.numWaiting++;
			// the last worker accessing notices that all other workers are
			// waiting. This indicates that all work is done.
			if (this.numWaiting >= TLCGlobals.getNumWorkers()) {
				if (isEmpty()) {
					this.numWaiting--;
					return false;
				}
				// TODO what happens if control flow exits without ever
				// notifying the checkpoint (mu.wait()) thread? In case
				// of distributed TLC, this is the main thread of
				// TLCServer.
				synchronized (this.mu) {
					this.mu.notify();
				}
			}
			try {
				this.wait();
			} catch (Exception e) {
				MP.printError(EC.GENERAL, (e.getMessage() == null) ? e.toString() : e.getMessage());
				System.exit(1);
			}
			this.numWaiting--;
			if (this.finish) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Signals all waiting {@link Worker} that all work is done. We can exit now.
	 */
	public synchronized void finishAll() {
		this.finish = true;
		this.notifyAll();
	}

	/**
	 * Suspends all access to the {@link StateQueue} for {@link Worker},
	 * potentially waiting for current accessing {@link Worker} to finish first.
	 * 
	 * @return False iff {@link #finish} is true, true otherwise
	 */
	public final boolean suspendAll() {
		boolean needWait = false;
		synchronized (this) {
			if (this.finish) {
				return false;
			}
			this.stop = true;
			needWait = needsWaiting();
		}
		while (needWait) {
			synchronized (this.mu) {
				try {
					// waiting here assumes that subsequently a worker
					// is going to wake us up by calling isAvail()
					this.mu.wait();
				} catch (Exception e) {
					MP.printError(EC.GENERAL, (e.getMessage() == null) ? e.toString() : e.getMessage());
					System.exit(1);
				}
			}
			synchronized (this) {
				if (this.finish) {
					return false;
				}
				needWait = needsWaiting();
			}
		}
		return true;
	}
	
	/**
	 * @return
	 */
	private boolean needsWaiting() {
		// no need to wait without workers present
		if (this.numWaiting < 1) {
			return false;
		}
		// if all workers wait at once, it's an indicate that all work is
		// done and suspending all workers can happen right away without
		// waiting.
		return this.numWaiting < TLCGlobals.getNumWorkers();
	}

	/**
	 * Resumes waiting {@link Worker} after a checkpoint
	 */
	public final synchronized void resumeAll() {
		this.stop = false;
		this.notifyAll();
	}

	/**
	 * This is a no-op in regular. The only case is, when a worker is stuck in
	 * {@link #isAvail()}, {@link #isEmpty}, {@link #stop} is false and
	 * {@link #numWaiting} > 0. Bottom-line, it is assumed to be side-effect
	 * free when workers behave correctly except for the single case when a
	 * remote worker dies unexpectedly.
	 * 
	 * @see http://bugzilla.tlaplus.net/show_bug.cgi?id=175
	 */
	public void resumeAllStuck() {
		// needsWaiting() read might have been incorrect if a TLCWorkerRMI dies
		// unexpectedly, thus this recovers a potentially stuck checkpointing
		// run.
		if (stop) {
			synchronized (mu) {
				mu.notifyAll();
			}
		}
		// 
		if (!stop && !isEmpty() && this.numWaiting > 0) {
			this.notifyAll();
		}
	}

	/* This method returns the size of the state queue. */
	public final int size() {
		return this.len;
	}

	/**
	 * @return true iff the inner queue does not contain states
	 */
	private boolean isEmpty() {
		return len < 1;
	}

	/* This method must be implemented in the subclass. */
	abstract void enqueueInner(TLCState state);

	/* This method must be implemented in the subclass. */
	abstract TLCState dequeueInner();

	/* Checkpoint. */
	public abstract void beginChkpt() throws IOException;

	public abstract void commitChkpt() throws IOException;

	public abstract void recover() throws IOException;
}
