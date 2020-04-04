// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:27 PST by lamport
//      modified on Tue Feb 13 18:38:24 PST 2001 by yuanyu

package tlc2.tool.queue;

import java.io.IOException;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.Worker;

/*
 * This class is identical to StateQueue except that it internally works
 * on byte[] whereas StateQueue's internal data is TLCStates. In other words,
 * serialization of TLCState to a byte[] occurs outside the critical section.
 */
public abstract class ByteArrayQueue implements IStateQueue {
	/**
	 * In model checking, this is the sequence of states waiting to be explored
	 * further. When the queue is empty, the checking is completed.
	 */
	protected long len = 0; // the queue length
	private int numWaiting = 0; // the number of waiting threads
	private volatile boolean finish = false; // terminate
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
	
	
	private final byte[] toBytes(final TLCState state) {
		try {
			final DiskByteArrayQueue.ByteValueOutputStream vos = new DiskByteArrayQueue.ByteValueOutputStream();
			state.write(vos);
			return vos.toByteArray();
		} catch (IOException notExpectedToHappen) {
			// With ByteArrayOutputStream
			notExpectedToHappen.printStackTrace();
		}
		return null;
	}
	
	private final byte[] toBytes(final TLCState state, final DiskByteArrayQueue.ByteValueOutputStream vos) {
		try {
			state.write(vos);
			return vos.toByteArray();
		} catch (IOException notExpectedToHappen) {
			// With ByteArrayOutputStream
			notExpectedToHappen.printStackTrace();
		}
		return null;
	}
	
	private final TLCState toState(final byte[] bytes) {
		try {
			final TLCState state = TLCState.Empty.createEmpty();
			state.read(new DiskByteArrayQueue.ByteValueInputStream(bytes));
			return state;
		} catch (IOException notExpectedToHappen) {
			// With ByteValueInputStream
			notExpectedToHappen.printStackTrace();
		}
		return null;
	}
	
	/* Enqueues the state. It is not thread-safe. */
	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#enqueue(tlc2.tool.TLCState)
	 */
	@Override
	public final void enqueue(final TLCState state) {
		enqueue(toBytes(state));
	}
	
	private final void enqueue(final byte[] state) {
		this.enqueueInner(state);
		this.len++;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#dequeue()
	 */
	@Override
	public final TLCState dequeue() {
		final byte[] bytes = dequeueRaw();
		if (bytes != null) {
			return toState(bytes);
		}
		return null;
	}
	
	private final byte[] dequeueRaw() {
		if (isEmpty()) {
			return null;
		}
		final byte[] state = this.dequeueInner();
		this.len--;
		return state;
	}

	/* Enqueues a state. Wake up any waiting thread. */
	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#sEnqueue(tlc2.tool.TLCState)
	 */
	@Override
	public final void sEnqueue(final TLCState state) {
		sEnqueue(toBytes(state));
	}
	
	private final synchronized void sEnqueue(final byte[] state) {
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
	@Override
	public final void sEnqueue(final TLCState[] states) {
		final byte[][] bytes = new byte[states.length][];
		for (int i = 0; i < states.length; i++) {
			bytes[i] = toBytes(states[i]);
		}
		sEnqueue(bytes);
	}
	
	private final synchronized void sEnqueue(final byte[][] states) {
		for (int i = 0; i < states.length; i++) {
			this.enqueueInner(states[i]);
		}
		this.len += states.length;
		if (this.numWaiting > 0 && !this.stop) {
			this.notifyAll();
		}
	}
	@Override
	public final void sEnqueue(final StateVec stateVec) {
		sEnqueue(stateVec, stateVec.size());
	}

//	@Override
	public final void sEnqueue(final StateVec stateVec, int n) {
		if (n == 0) {
			return;
		}
		
		final DiskByteArrayQueue.ByteValueOutputStream vos = new DiskByteArrayQueue.ByteValueOutputStream();
		final byte[][] bytes = new byte[n][];
		for (int i = 0; i < stateVec.size(); i++) {
			final TLCState state = stateVec.elementAt(i);
			if (state != null) {
				bytes[n - 1] = toBytes(state, vos);
				n--;
			}
		}
		sEnqueue(bytes);
	}
	
	@Override
	public final TLCState sPeek() {
		final byte[] bytes = sPeekRaw();
		if (bytes != null) {
			return toState(bytes);
		}
		return null;
	}
		
	private final synchronized byte[] sPeekRaw() {
		if (this.isAvail()) {
			return this.peekInner();
		}
		return null;
	}

	/* Return the first element in the queue. Wait if empty. */
	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#sDequeue()
	 */
	@Override
	public final TLCState sDequeue() {
		final byte[] bytes = sDequeueRaw();
		if (bytes != null) {
			return toState(bytes);
		}
		return null;
	}
	
	private final synchronized byte[] sDequeueRaw() {
		if (this.isAvail()) {
			final byte[] state = this.dequeueInner();
			assert state != null : "Null state found on queue";
			this.len--;
			return state;
		}
		return null;
	}
	
	@Override
	public final TLCState[] sDequeue(int cnt) {
		final byte[][] bytes = sDequeueRaw(cnt);
		if (bytes != null) {
			final TLCState[] array = new TLCState[cnt];
			for (int i = 0; i < array.length; i++) {
				array[i] = toState(bytes[i]);
			}
			return array;
		}
		return null;
	}

	private final synchronized byte[][] sDequeueRaw(int cnt) {
		assert cnt > 0 : "Nonpositive number of states requested.";
		if (this.isAvail()) {
			if (cnt > len) {
				// in this case, casting len to int is safe 
				cnt = (int) len;
			}
			final byte[][] states = new byte[cnt][];
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
			final byte[][] res = new byte[idx][];
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
		/*
		 * isAvail is only called from within sDequeue() and sDequeue(..) and
		 * thus is always synchronized on this.
		 */
		
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
	@Override
	public synchronized void finishAll() {
		this.finish = true;
		// Notify all other worker threads.
		this.notifyAll();
		// Need to wake main thread that waits (mu.wait()) to suspend access to
		// the squeue (see suspendAll). The main thread might attempt to do its
		// periodic work (tlc2.tool.ModelChecker.doPeriodicWork()) the moment
		// all worker threads finish. Since suspendAll assumes the main thread
		// is woken up (potentially) multiple times from sleeping indefinitely
		// in the while loop before it finally returns after locking the
		// StateQueue, we have to live up to this assumption.
		//
		// synchronized(this.mu) does not block when the main thread waits on
		// this.mu in suspend all. We merely have to follow proper thread access.
		synchronized (this.mu) {
			// Technically notify() would do.
			this.mu.notify();
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#suspendAll()
	 */
	@Override
	public final boolean suspendAll() {
		boolean needWait = false;
		synchronized (this) {
			if (this.finish) {
				return false;
			}
			this.stop = true;
			needWait = needsWaiting();
		}
		// Wait for all worker threads to stop.
		while (needWait) {
			synchronized (this.mu) {
				try {
					// finishAll & suspendAll race:
					//
					// suspendAll from main is on the heels of finishAll, but
					// not quite as fast. SuspendAll's synchronized(this.mu)
					// is executed one clock tick after finishAll's thus waiting
					// for finishAll() to notify all waiters of this.mu.
					// With main being the only potential waiter in the system
					// nobody gets notified and the lock on this released
					// subsequently.
					// Now it's suspendAll's turn. It acquires the lock on
					// this.mu and immediately after goes to wait on it
					// (this.mu) to be waken by worker threads eventually.
					// Unfortunately, there are none left in the system. All
					// have long finishedAll.
					//
					// The fix is to check the this.finish variable one more
					// time directly after suspendAll acquires the lock this.mu,
					// it checks if it still has to wait for workers. To make
					// sure it reads the most recent value, it's declared
					// volatile to establish a happens-before relation (since
					// Java5's memory model) between workers and main. Otherwise
					// the VM might decide to let main read a cached value of
					// false of this.finish.
					if (this.finish) {
						return false;
					}
					// waiting here assumes that subsequently a worker
					// is going to wake us up by calling isAvail() or
					// this.mu.notify*()
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
	@Override
	public final synchronized void resumeAll() {
		this.stop = false;
		this.notifyAll();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.queue.IStateQueue#resumeAllStuck()
	 */
	@Override
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
	@Override
	public final long size() {
		return this.len;
	}

	/**
	 * @return true iff the inner queue does not contain states
	 */
	@Override
	public boolean isEmpty() {
		return len < 1;
	}

	/* This method must be implemented in the subclass. */
	abstract void enqueueInner(byte[] state);

	/* This method must be implemented in the subclass. */
	abstract byte[] dequeueInner();

	/* This method must be implemented in the subclass. */
	abstract byte[] peekInner();
	
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
