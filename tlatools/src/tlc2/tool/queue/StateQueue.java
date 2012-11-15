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

/**
 * 
 */
// TODO-MAK - Why do consumer/producer game on StateQueue when workers could
// maintaine thread local StateQueue until it gets empty?
public abstract class StateQueue implements IStateQueue {
	/**
	 * In model checking, this is the sequence of states waiting to be explored
	 * further. When the queue is empty, the checking is completed.
	 */
	protected long len = 0; // the queue length
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
	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#enqueue(tlc2.tool.TLCState)
	 */
	public final void enqueue(final TLCState state) {
		this.enqueueInner(state);
		this.len++;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#dequeue()
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
	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#sEnqueue(tlc2.tool.TLCState)
	 */
	public final synchronized void sEnqueue(final TLCState state) {
		this.enqueueInner(state);
		this.len++;
		if (this.numWaiting > 0 && !this.stop) {
			this.notifyAll();
		}
	}

	/* Enqueues a list of states. Wake up any waiting thread. */
	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#sEnqueue(tlc2.tool.TLCState[])
	 */
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
	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#sDequeue()
	 */
	public final synchronized TLCState sDequeue() {
		if (this.isAvail()) {
			final TLCState state = this.dequeueInner();
			// LL modified error message on 7 April 2012
			Assert.check(state != null, "Null state found on queue");
			this.len--;
			return state;
		}
		return null;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#sDequeue(int)
	 */
	public final synchronized TLCState[] sDequeue(int cnt) {
		Assert.check(cnt > 0, "Nonpositive number of states requested.");
		if (this.isAvail()) {
			if (cnt > len) {
				// in this case, casting len to int is safe 
				cnt = (int) len;
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
				MP.printError(EC.GENERAL, "making a worker wait for a state from the queue", e);  // LL changed call 7 April 2012
				System.exit(1);
			}
			this.numWaiting--;
			if (this.finish) {
				return false;
			}
		}
		return true;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#finishAll()
	 */
	public synchronized void finishAll() {
		this.finish = true;
		this.notifyAll();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#suspendAll()
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
					MP.printError(EC.GENERAL, "waiting for a worker to wake up", e);  // LL changed call 7 April 2012
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
		//MAK 04/2012: Commented to fix an EOFException when liveness checking is enabled 
//		// no need to wait without workers present
//		if (this.numWaiting < 1) {
//			return false;
//		}
		// if all workers wait at once, it indicates that all work is
		// done and suspending all workers can happen right away without
		// waiting.
		return this.numWaiting < TLCGlobals.getNumWorkers();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#resumeAll()
	 */
	public final synchronized void resumeAll() {
		this.stop = false;
		this.notifyAll();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#resumeAllStuck()
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
			synchronized (this) {
				this.notifyAll();
			}
		}
	}

	/* This method returns the size of the state queue. */
	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#size()
	 */
	public final long size() {
		return this.len;
	}

	/**
	 * @return true iff the inner queue does not contain states
	 */
	public boolean isEmpty() {
		return len < 1;
	}

	/* This method must be implemented in the subclass. */
	abstract void enqueueInner(TLCState state);

	/* This method must be implemented in the subclass. */
	abstract TLCState dequeueInner();

	/* Checkpoint. */
	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#beginChkpt()
	 */
	public abstract void beginChkpt() throws IOException;

	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#commitChkpt()
	 */
	public abstract void commitChkpt() throws IOException;

	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#recover()
	 */
	public abstract void recover() throws IOException;
}
