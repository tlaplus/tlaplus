// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:34 PST by lamport  
//      modified on Fri Mar  2 23:46:22 PST 2001 by yuanyu   

package tlc2.tool.distributed;

import java.rmi.RemoteException;

import tlc2.TLCGlobals;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateVec;
import tlc2.tool.WorkerException;
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
  /**
   * TLC server threads manage the set of existing TLC workers.
   */
  private final static int BlockSize = 1024;

  public TLCServerThread(int id, TLCWorkerRMI worker, TLCServer tlc) {
    super(id);
    this.worker = worker;
    this.tlcServer = tlc;
  }

  private TLCWorkerRMI worker;
  private TLCServer tlcServer;

  public final TLCWorkerRMI getWorker() { return this.worker; }

  public final void setWorker(TLCWorkerRMI worker) {
    this.worker = worker;
  }

  /**
   * This method gets a state from the queue, generates all the possible
   * next states of the state, checks the invariants, and updates the state
   * set and state queue.
   */
  public void run() {
    TLCGlobals.incNumWorkers(1);
    TLCStateVec[] newStates = null;
    LongVec[] newFps = null;

    try {
      while (true) {
	TLCState[] states = this.tlcServer.stateQueue.sDequeue(BlockSize);
	if (states == null) {
	  synchronized(this.tlcServer) {
            this.tlcServer.setDone();
	    this.tlcServer.notify();
	  }
	  this.tlcServer.stateQueue.finishAll();
	  return;
	}
    
	boolean workDone = false;
	while (!workDone) {
	  try {
	    Object[] res = this.worker.getNextStates(states);
	    newStates = (TLCStateVec[])res[0];
	    newFps = (LongVec[])res[1];
	    workDone = true;
	  }
	  catch (RemoteException e) {
	    if (!this.tlcServer.reassignWorker(this)) {
	      ToolIO.err.println("Error: No TLC worker is available. Exit.");
	      System.exit(0);	      
	    }
	  }
	  catch (NullPointerException e) {
	    if (!this.tlcServer.reassignWorker(this)) {
	      ToolIO.err.println("Error: No TLC worker is available. Exit.");
	      System.exit(0);
	    }
	  }
	}

	BitVector[] visited = this.tlcServer.fpSetManager.putBlock(newFps);
	for (int i = 0; i < visited.length; i++) {
	  BitVector.Iter iter = new BitVector.Iter(visited[i]);
	  int index;
	  while ((index = iter.next()) != -1) {
	    TLCState state = newStates[i].elementAt(index);
	    long fp = newFps[i].elementAt(index);
	    state.uid = this.tlcServer.trace.writeState(state.uid, fp);
	    this.tlcServer.stateQueue.sEnqueue(state);
	  }
	}
      }
    }
    catch (Throwable e) {
      TLCState state1 = null, state2 = null;
      if (e instanceof WorkerException) {
	state1 = ((WorkerException)e).state1;
	state2 = ((WorkerException)e).state2;
      }
      if (this.tlcServer.setErrState(state1, true)) {
	ToolIO.err.println(e.getMessage());
	if (state1 != null) {
	  try {
	    ToolIO.err.println("\nThe behavior up to this point is:");
	    this.tlcServer.trace.printTrace(state1.uid, state1, state2);
	  }
	  catch (Exception e1) { System.err.println(e1.getMessage()); }
	}
	this.tlcServer.stateQueue.finishAll();
	synchronized(this.tlcServer) { this.tlcServer.notify(); }
      }
    }
  }
}
