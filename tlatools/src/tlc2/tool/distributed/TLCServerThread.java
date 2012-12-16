// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:34 PST by lamport  
//      modified on Fri Mar  2 23:46:22 PST 2001 by yuanyu   
package tlc2.tool.distributed;

import java.io.EOFException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.io.Writer;
import java.net.URI;
import java.rmi.RemoteException;
import java.util.Date;
import java.util.Timer;
import java.util.TimerTask;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.atomic.AtomicBoolean;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateVec;
import tlc2.tool.WorkerException;
import tlc2.tool.distributed.selector.IBlockSelector;
import tlc2.tool.fp.FPSet;
import tlc2.tool.queue.IStateQueue;
import tlc2.tool.queue.StateQueue;
import tlc2.util.BitVector;
import tlc2.util.IdThread;
import tlc2.util.LongVec;

public class TLCServerThread extends IdThread {
	private static int COUNT = 0;
	/**
	 * Runtime statistics about states send and received by and from the remote
	 * worker. These stats are shown at the end of model checking for every
	 * worker thread.
	 */
	private int receivedStates, sentStates;
	/**
	 * {@link TLCWorker}s maintain a worker-local fingerprint cache. The hit
	 * ratio is kept here for final statistics. A negative value indicates that
	 * the statistic has not been gathered yet.
	 */
	private double cacheRateHitRatio = -1L;
	/**
	 * An {@link IBlockSelector} tunes the amount of states send to a remote
	 * worker. Depending on its concrete implementation it might employ runtime
	 * statistics to assign the ideal amount of states.
	 * 
	 * @see TLCServerThread#states
	 */
	private final IBlockSelector selector;
	/**
	 * Current unit of work or null
	 * 
	 * @see TLCServerThread#selector
	 */
	private TLCState[] states = new TLCState[0];
	/**
	 * Periodically check the remote worker's aliveness by spawning a
	 * asynchronous task that is automatically scheduled by the JVM for
	 * re-execution in the defined interval.
	 * <p>
	 * It is the tasks responsibility to detect a stale worker and disconnect
	 * it.
	 * 
	 * @see TLCServerThread#keepAliveTimer
	 */
	private final TLCTimerTask task;
	/**
	 * @see TLCServerThread#task
	 */
	private final Timer keepAliveTimer;
	/**
	 * Synchronized flag used to indicate the correct amount of workers to
	 * TCLGlobals.
	 * 
	 * Either {@link TLCServerThread#run()} or
	 * {@link TLCServerThread#keepAliveTimer} will flip to false causing
	 * subsequent calls to
	 * {@link TLCServerThread#handleRemoteWorkerLost(StateQueue)} to be a noop.
	 * 
	 * Synchronization is required because {@link TLCServerThread#run()} and
	 * {@link TLCTimerTask#run()} are executed as two separate threads.
	 */
	private final AtomicBoolean cleanupGlobals = new AtomicBoolean(true);
	/**
	 * An {@link ExecutorService} used to parallelize calls to the _distributed_
	 * fingerprint set servers ({@link FPSet}).
	 * <p>
	 * The fingerprint space is partitioned across all {@link FPSet} servers and
	 * thus can be accessed concurrently.
	 */
	private final ExecutorService executorService;
	/**
	 * An RMI proxy for the remote worker.
	 * 
	 * @see TLCServerThread#tlcServer
	 */
	private final TLCWorkerRMI worker;
	/**
	 * The {@link TLCServer} master this {@link TLCServerThread} provides the
	 * service of handling a single remote worker. A {@link TLCServer} uses n
	 * {@link TLCWorker}s to calculate the next state relation. To invoke
	 * workers concurrently, it spawns a {@link TLCServerThread} for each
	 * {@link TLCWorkerRMI} RMI proxy.
	 * <p>
	 * {@link TLCServer} and {@link TLCWorkerRMI} form a 1:n mapping and
	 * {@link TLCServerThread} is this mapping.
	 * 
	 * @see TLCServerThread#worker
	 */
	private final TLCServer tlcServer;
	/**
	 * Remote worker's address used to label local threads.
	 */
	private URI uri;

	public TLCServerThread(TLCWorkerRMI worker, URI aURI, TLCServer tlc, ExecutorService es, IBlockSelector aSelector) {
		super(COUNT++);
		this.executorService = es;
		this.tlcServer = tlc;
		this.selector = aSelector;
		this.uri = aURI;

		// Create Timer early to avoid NPE in handleRemoteWorkerLost (it tries to cancel the timer)
		keepAliveTimer = new Timer("TLCWorker KeepAlive Timer ["
				+ uri.toASCIIString() + "]", true);
		
		// Wrap the TLCWorker with a SmartProxy. A SmartProxy's responsibility
		// is to measure the RTT spend to transfer states back and forth.
		this.worker = new TLCWorkerSmartProxy(worker);

		// Prefix the thread name with a fixed string and a counter.
		// This part is used by the external Munin based statistics software to
		// gather thread contention stats.
		final String i = String.format("%03d", myGetId());
		setName(TLCServer.THREAD_NAME_PREFIX + i + "-[" + uri.toASCIIString() + "]");
		
		// schedule a timer to periodically (60s) check server aliveness
		task = new TLCTimerTask();
		keepAliveTimer.schedule(task, 10000, 60000);
	}

	/**
	 * This method gets a state from the queue, generates all the possible next
	 * states of the state, checks the invariants, and updates the state set and
	 * state queue.
	 */
	public void run() {
		TLCGlobals.incNumWorkers();
		TLCStateVec[] newStates = null;
		LongVec[] newFps = null;

		final IStateQueue stateQueue = this.tlcServer.stateQueue;
		try {
			START: while (true) {
				// blocks until more states available or all work is done
				states = selector.getBlocks(stateQueue, worker);
				if (states == null) {
					synchronized (this.tlcServer) {
						this.tlcServer.setDone();
						this.tlcServer.notify();
					}
					stateQueue.finishAll();
					return;
				}

				// without initial states no need to bother workers
				if (states.length == 0) {
					continue;
				}

				// count statistics
				sentStates += states.length;

				// real work happens here:
				// worker computes next states for states
				boolean workDone = false;
				while (!workDone) {
					try {
						final NextStateResult res = this.worker.getNextStates(states);
						newStates = res.getNextStates();
						receivedStates += newStates[0].size();
						newFps = res.getNextFingerprints();
						workDone = true;
						task.setLastInvocation(System.currentTimeMillis());
						// Read remote worker cache hits which correspond to
						// states skipped
						tlcServer.addStatesGeneratedDelta(res.getStatesComputedDelta());
					} catch (RemoteException e) {
						// If a (remote) {@link TLCWorkerRMI} fails due to the
						// amount of new states we have sent it, try to lower
						// the amount of states
						// and re-send (until we just send a single state)
						if (isRecoverable(e) && states.length > 1) {
							MP.printMessage(
									EC.TLC_DISTRIBUTED_EXCEED_BLOCKSIZE,
									Integer.toString(states.length / 2));
							// states[] exceeds maximum transferable size
							// (add states back to queue and retry)
							stateQueue.sEnqueue(states);
							// half the maximum size and use it as a limit from
							// now on
							selector.setMaxTXSize(states.length / 2);
							// go back to beginning
							continue START;
						} else { 
							// non recoverable errors, exit...
							MP.printMessage(
									EC.TLC_DISTRIBUTED_WORKER_LOST,
									getUri().toString());
							handleRemoteWorkerLost(stateQueue);
							return;
						}
					} catch (NullPointerException e) {
						MP.printMessage(EC.TLC_DISTRIBUTED_WORKER_LOST,
								// have the stack trace on a newline
								"\n" + throwableToString(e));
						handleRemoteWorkerLost(stateQueue);
						return;
					}
				}

				// add fingerprints to fingerprint manager (delegates to
				// corresponding fingerprint server)
				// (Why isn't this done by workers directly?
				// -> because if the worker crashes while computing states, the
				// fp set would be inconsistent => making it an "atomic"
				// operation)
				BitVector[] visited = this.tlcServer.fpSetManager
						.putBlock(newFps, executorService);

				// recreate newly computed states and add them to queue
				for (int i = 0; i < visited.length; i++) {
					BitVector.Iter iter = new BitVector.Iter(visited[i]);
					int index;
					while ((index = iter.next()) != -1) {
						TLCState state = newStates[i].elementAt(index);
						// write state id and state fp to .st file for
						// checkpointing
						long fp = newFps[i].elementAt(index);
						state.uid = this.tlcServer.trace.writeState(state, fp);
						// add state to state queue for further processing
						stateQueue.sEnqueue(state);
					}
				}
			}
		} catch (Throwable e) {
			TLCState state1 = null, state2 = null;
			if (e instanceof WorkerException) {
				state1 = ((WorkerException) e).state1;
				state2 = ((WorkerException) e).state2;
			}
			if (this.tlcServer.setErrState(state1, true)) {
				MP.printError(EC.GENERAL, e);
				if (state1 != null) {
					try {
						this.tlcServer.trace.printTrace(state1, state2);
					} catch (Exception e1) {
						MP.printError(EC.GENERAL, e1);
					}
				}
				stateQueue.finishAll();
				synchronized (this.tlcServer) {
					this.tlcServer.notify();
				}
			}
		} finally {
			try {
				cacheRateHitRatio = worker.getCacheRateRatio();
			} catch (RemoteException e) {
				// Remote worker might crash after return the last next
				// state computation result but before the cache rate hit
				// ratio statistic could be read. If this is the case the
				// final statistic will be reported as negative indicating
				// that it failed to read the statistic.
				MP.printWarning(
						EC.GENERAL,
						"Failed to read remote worker cache statistic (Expect to see a negative chache hit rate. Does not invalidate model checking results)");
			}
			keepAliveTimer.cancel();
			states = new TLCState[0];
			// not calling TLCGlobals#decNumWorkers here because at this point
			// TLCServer is shutting down anyway
		}
	}

	/**
	 * A recoverable error/exception is defined to be a case where the
	 * {@link TLCWorkerRMI} can continue to work if {@link TLCServer} sends less
	 * new states to process.
	 */
	private boolean isRecoverable(final Exception e) {
		final Throwable cause = e.getCause();
		return ((cause instanceof EOFException && cause.getMessage() == null) || (cause instanceof RemoteException && cause
				.getCause() instanceof OutOfMemoryError));
	}

	private String throwableToString(final Exception e) {
		final Writer result = new StringWriter();
		final PrintWriter printWriter = new PrintWriter(result);
		e.printStackTrace(printWriter);
		return result.toString();
	}

	/**
	 * Handles the case of a disconnected remote worker
	 * 
	 * @param stateQueue
	 */
	private void handleRemoteWorkerLost(final IStateQueue stateQueue) {
		// Cancel the keepAliveTimer which might still be running if an
		// exception in the this run() method has caused handleRemoteWorkerLost
		// to be called.
		keepAliveTimer.cancel();
		
		// This call has to be idempotent, otherwise we see bugs as in 
		// https://bugzilla.tlaplus.net/show_bug.cgi?id=234
		//
		// Prevent second invocation of worker de-registration which stamps from
		// a race condition between the TimerTask (that periodically checks
		// server aliveness) and the exception handling that kicks in when the
		// run() method catches an RMI exception.
		if (cleanupGlobals.compareAndSet(true, false)) {

			// De-register TLCServerThread at the main server thread locally
			tlcServer.removeTLCServerThread(this);
			
			// Return the undone worklist (if any)
			if (stateQueue != null) {
				stateQueue.sEnqueue(states != null ? states : new TLCState[0]);
			}
			
			// Reset states to empty array to signal to TLCServer that we are not
			// processing any new states. Otherwise statistics will incorrectly
			// count this TLCServerThread as actively calculating states.
			states = new TLCState[0];
			
			// Before decrementing the worker count, notify all waiters on
			// stateQueue to re-evaluate the while loop in isAvail(). The demise
			// of this worker (who potentially was the lock owner) might causes
			// another consumer to leave the while loop (become a consumer).
			//
			// This has to happen _prior_ to calling decNumWorkers. Otherwise
			// we decrement the total number and the active count by one
			// simultaneously, leaving isAvail without effect.
			//
			// This is to work around a design bug in
			// tlc2.tool.queue.StateQueue's impl. Other IStateQueue impls should
			// hopefully not be affected by calling notifyAll on them though.
			synchronized (stateQueue) {
				stateQueue.notifyAll();
			}
			
			TLCGlobals.decNumWorkers();
		}
	}

	/**
	 * @return The current amount of states the corresponding worker is
	 *         computing on
	 */
	public int getCurrentSize() {
		return states.length;
	}

	/**
	 * @return the url
	 */
	public URI getUri() {
		return this.uri;
	}

	/**
	 * @return the receivedStates
	 */
	public int getReceivedStates() {
		return receivedStates;
	}

	/**
	 * @return the sentStates
	 */
	public int getSentStates() {
		return sentStates;
	}
	
	/**
	 * @return The hit ratio of the worker-local fingerprint cache.
	 */
	public double getCacheRateRatio() {
		return cacheRateHitRatio;
	}

	// ************************************//

	private class TLCTimerTask extends TimerTask {
		/**
		 * Timestamp of last successful remote invocation 
		 */
		private long lastInvocation = 0L;

		/* (non-Javadoc)
		 * @see java.util.TimerTask#run()
		 */
		public void run() {
			// Check if the last invocation happened within the last minute. If
			// not, check the worker's aliveness and dispose of it if indeed
			// lost.
			long now = new Date().getTime();
			if (lastInvocation == 0 || (now - lastInvocation) > 60000) {
				try {
					if (!worker.isAlive()) {
						handleRemoteWorkerLost(tlcServer.stateQueue);
					}
				} catch (RemoteException e) {
					handleRemoteWorkerLost(tlcServer.stateQueue);
				}
			}
		}

		/**
		 * @param lastInvocation the lastInvocation to set
		 */
		public void setLastInvocation(long lastInvocation) {
			this.lastInvocation = lastInvocation;
		}
	}
}
