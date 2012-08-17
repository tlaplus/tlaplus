// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 14:01:40 PST by lamport  
//      modified on Wed Dec  5 15:35:42 PST 2001 by yuanyu   

package tlc2.tool;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.queue.IStateQueue;
import tlc2.util.IdThread;
import tlc2.util.ObjLongTable;
import tlc2.value.Value;

public class Worker extends IdThread implements IWorker {
	/**
   * Multi-threading helps only when running on multiprocessors. TLC
   * can pretty much eat up all the cycles of a processor running
   * single threaded.  We expect to get linear speedup with respect
   * to the number of processors.
	 */
	private ModelChecker tlc;
	private IStateQueue squeue;
	private ObjLongTable astCounts;
	private Value[] localValues;

	// SZ Feb 20, 2009: changed due to super type introduction
	public Worker(int id, AbstractChecker tlc) {
		super(id);
		// SZ 12.04.2009: added thread name
		this.setName("TLC Worker " + id);
		this.tlc = (ModelChecker) tlc;
		this.squeue = this.tlc.theStateQueue;
		this.astCounts = new ObjLongTable(10);
		this.localValues = new Value[4];
		this.setName("TLCWorkerThread-" + String.format("%03d", id));
	}

  public final ObjLongTable getCounts() { return this.astCounts; }

	public Value getLocalValue(int idx) {
		if (idx < this.localValues.length) {
			return this.localValues[idx];
		}
		return null;
	}

	public void setLocalValue(int idx, Value val) {
		if (idx >= this.localValues.length) {
			Value[] vals = new Value[idx + 1];
			System.arraycopy(this.localValues, 0, vals, 0, this.localValues.length);
			this.localValues = vals;
		}
		this.localValues[idx] = val;
	}

	/**
   * This method gets a state from the queue, generates all the
   * possible next states of the state, checks the invariants, and
   * updates the state set and state queue.
	 */
	public final void run() {
		TLCState curState = null;
		try {
			while (true) {
				curState = (TLCState) this.squeue.sDequeue();
				if (curState == null) {
					synchronized (this.tlc) {
						this.tlc.setDone();
						this.tlc.notify();
					}
					this.squeue.finishAll();
					return;
				}
	if (this.tlc.doNext(curState, this.astCounts)) return;
				}
			}
    catch (Throwable e) {
			// Something bad happened. Quit ...
			// Assert.printStack(e);
			synchronized (this.tlc) {
				if (this.tlc.setErrState(curState, null, true)) {
	    MP.printError(EC.GENERAL, e);  // LL changed call 7 April 2012
				}
				this.squeue.finishAll();
				this.tlc.notify();
			}
			return;
		}
	}

}
