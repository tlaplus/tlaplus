// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:34 PST by lamport  
//      modified on Fri Mar  2 23:46:22 PST 2001 by yuanyu   

package tlc2.tool.distributed;

import java.rmi.RemoteException;
import java.util.Date;
import java.util.concurrent.BrokenBarrierException;
import java.util.concurrent.CyclicBarrier;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateVec;
import tlc2.tool.WorkerException;
import tlc2.tool.queue.StateQueue;
import tlc2.util.BitVector;
import tlc2.util.IdThread;
import tlc2.util.LongVec;
import util.ToolIO;

/**
 * 
 * @deprecated not used currently
 * @version $Id$
 */
public class TLCServerThread extends IdThread {
	private static final String BLOCK_SIZE = "tlc2.tool.distributed.TLCServerThread.BlockSize";
	/**
	 * TLC server threads manage the set of existing TLC workers.
	 */
	private final static int BlockSize = Integer.getInteger(BLOCK_SIZE, 1024);
	private CyclicBarrier barrier;
	/**
	 * Identifies the worker
	 */
	private String url = "";
	private int receivedStates, sentStates;

	public TLCServerThread(int id, TLCWorkerRMI worker, String url, TLCServer tlc, CyclicBarrier aBarrier) {
		super(id);
		this.worker = worker;
		this.url  = url;
		this.tlcServer = tlc;
		this.barrier = aBarrier;
	}

	private TLCWorkerRMI worker;
	private TLCServer tlcServer;

	public final TLCWorkerRMI getWorker() {
		return this.worker;
	}

	public final void setWorker(TLCWorkerRMI worker) {
		this.worker = worker;
	}

	/**
	 * This method gets a state from the queue, generates all the possible next
	 * states of the state, checks the invariants, and updates the state set and
	 * state queue.
	 */
	public void run() {
		waitOnBarrier();
		
		TLCGlobals.incNumWorkers(1);
		TLCStateVec[] newStates = null;
		LongVec[] newFps = null;

		final StateQueue stateQueue = this.tlcServer.stateQueue;
		try {
			while (true) {
				TLCState[] states = stateQueue
						.sDequeue(getBlockSize(stateQueue.size()));
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

				boolean workDone = false;
				while (!workDone) {
					try {
						long start = System.currentTimeMillis();
						Object[] res = this.worker.getNextStates(states);
						long end = System.currentTimeMillis();
						newStates = (TLCStateVec[]) res[0];
						receivedStates += newStates[0].size();
						newFps = (LongVec[]) res[1];
						workDone = true;
						ToolIO.out.println(new Date() + " Worker: " + url
								+ " Sent: " + states.length + " Rcvd: "
								+ newStates[0].size() + " Time: " + (end - start)
								+ " ms");
					} catch (RemoteException e) {
						if (!this.tlcServer.reassignWorker(this)) {
							ToolIO.out
									.println("Error: No TLC worker is available. Exit.");
							return;
						}
					} catch (NullPointerException e) {
						if (!this.tlcServer.reassignWorker(this)) {
							ToolIO.out
									.println("Error: No TLC worker is available. Exit.");
							return;
						}
					}
				}

				BitVector[] visited = this.tlcServer.fpSetManager
						.putBlock(newFps);
				for (int i = 0; i < visited.length; i++) {
					BitVector.Iter iter = new BitVector.Iter(visited[i]);
					int index;
					while ((index = iter.next()) != -1) {
						TLCState state = newStates[i].elementAt(index);
						long fp = newFps[i].elementAt(index);
						state.uid = this.tlcServer.trace.writeState(state.uid,
								fp);
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
						ToolIO.out
								.println("\nThe behavior up to this point is:");
						this.tlcServer.trace.printTrace(state1.uid, state1,
								state2);
					} catch (Exception e1) {
						System.err.println(e1.getMessage());
					}
				}
				stateQueue.finishAll();
				synchronized (this.tlcServer) {
					this.tlcServer.notify();
				}
			}
		}
	}

	/**
	 * Calculates the number of states a worker should be assigned. This
	 * calculation is based on the current number of workers registered with the
	 * server assigning each worker 1/N of the statequeue with N being the
	 * current amount of workers.
	 *  
	 * If the system property {@link TLCServer}
	 * .expectedWorkercount is set to -1, a fixed block size will be used. This
	 * can be configured by setting BLOCK_SIZE to the intended value.
	 * 
	 * The block size essentially load balances the workers by deciding how much
	 * work they get assigned.
	 * 
	 * @param size
	 *            The current size of the state queue.
	 * @return The intended block size
	 */
	private int getBlockSize(int size) {
		if(TLCServer.expectedWorkerCount == -1) {
			return BlockSize;
		} else {
			return (int) Math
					.ceil(size * (1.0 / tlcServer.getWorkerCount()));
		}
	}

	/**
	 * Causes this thread to wait for all other worker threads before it starts
	 * computing states. The barrier may be null in which case threads start
	 * computing next states immediately after creation.
	 */
	private void waitOnBarrier() {
		try {
			if(barrier != null)
				barrier.await();
		} catch (InterruptedException e2) {
			e2.printStackTrace();
		} catch (BrokenBarrierException e2) {
			e2.printStackTrace();
		}
	}

	/**
	 * @return the url
	 */
	public String getUrl() {
		return url;
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
}
