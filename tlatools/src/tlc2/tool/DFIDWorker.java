// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tlc2.tool;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.output.StatePrinter;
import tlc2.tool.fp.dfid.FPIntSet;
import tlc2.util.IdThread;
import tlc2.util.LongVec;
import tlc2.util.ObjLongTable;
import tlc2.util.RandomGenerator;

public class DFIDWorker extends IdThread implements IWorker {
  /**
   * Multi-threading helps only when running on multiprocessors. TLC
   * can pretty much eat up all the cycles of a processor running
   * single threaded.  We expect to get linear speedup with respect
   * to the number of processors.
   */
  private DFIDModelChecker tlc;
  private RandomGenerator rng;
  private TLCState[] stateStack;
  private long[] fpStack;
  private StateVec[] succStateStack;
  private LongVec[] succFPStack;
  private FPIntSet theFPSet;
  private TLCState[] theInitStates;
  private long[] theInitFPs;
  private int initLen;
  private ObjLongTable astCounts;
  private int toLevel;
  private int curLevel;
  private int stopCode;
  private boolean moreLevel;

  // SZ Feb 20, 2009: changes due to the introduced super type
  public DFIDWorker(int id, int toLevel, AbstractChecker tlc) {
    super(id);
    this.tlc = (DFIDModelChecker) tlc;
    this.rng = new RandomGenerator();
    this.rng.setSeed(this.rng.nextLong());
    this.stateStack = new TLCState[TLCGlobals.DFIDMax];
    this.fpStack = new long[TLCGlobals.DFIDMax];
    this.succStateStack = new StateVec[TLCGlobals.DFIDMax];
    this.succFPStack = new LongVec[TLCGlobals.DFIDMax];
    for (int i = 0; i < TLCGlobals.DFIDMax; i++) {
      this.succStateStack[i] = new StateVec(1);
      this.succFPStack[i] = new LongVec(1);
    }
    this.theFPSet = this.tlc.theFPSet;
    this.initLen = this.tlc.theInitStates.length;
    this.theInitStates = new TLCState[this.initLen];
    this.theInitFPs = new long[this.initLen];
    System.arraycopy(this.tlc.theInitStates, 0, this.theInitStates, 0, this.initLen);
    System.arraycopy(this.tlc.theInitFPs, 0, this.theInitFPs, 0, this.initLen);
    this.astCounts = new ObjLongTable(10);    
    this.toLevel = toLevel;
    this.curLevel = 0;
    this.stopCode = 0;
    this.moreLevel = false;
  }

  public final ObjLongTable getCounts() { return this.astCounts; }

  public final void setStop(int code) { this.stopCode = code; }

  public final boolean isTerminated() { return this.stopCode == 2; }

  public final boolean hasMoreLevel() { return this.moreLevel; }
  
  /**
   * Choose a random initial state that has not been done. Return the
   * index of the chosen state. Return -1 if there is no such kind of
   * initial state.
   */
  private final int getInit() {
    while (this.initLen > 0) {
      int index = (int)Math.floor(this.rng.nextDouble() * this.initLen);
      long fp = this.theInitFPs[index];
      int status = this.theFPSet.getStatus(fp);

      // Assert.check(status != FPIntSet.NEW);
      if (!FPIntSet.isCompleted(status)) {
	return index;
      }

      this.initLen--;
      this.theInitStates[index] = this.theInitStates[this.initLen];
      this.theInitFPs[index] = this.theInitFPs[this.initLen];
    }
    return -1;
  }

  /**
   * Choose a random next state from curState that has not been done.
   * Return the index of the chosen state. Return -1 if there is no
   * such kind of next states.
   */
  private final int getNext(TLCState curState, long cfp) {
    StateVec succStates = this.succStateStack[this.curLevel-1];
    LongVec succFPs = this.succFPStack[this.curLevel-1];
    int len = succFPs.size();

    while (len > 0) {
      int index = (int)Math.floor(this.rng.nextDouble() * len);
      long fp = succFPs.elementAt(index);
      int status = this.theFPSet.getStatus(fp);

      // Assert.check(status != FPIntSet.NEW);
      if (!FPIntSet.isCompleted(status) &&
	  this.curLevel < FPIntSet.getLevel(status)) {
	return index;
      }
      succStates.removeElement(index);
      succFPs.removeElement(index);
      len--;
    }
    return -1;
  }

  /**
   * Prints the stacktrace
   * @param code error code
   * @param params params
   * @param s1 
   * @param s2
   */
  public final void printTrace(int errorCode, String[] parameters, TLCState s1, TLCState s2) 
  {
      MP.printError(errorCode, parameters);
      MP.printError(EC.TLC_BEHAVIOR_UP_TO_THIS_POINT);
      int idx = 0;
      while (idx < this.curLevel) 
      {
          StatePrinter.printState(this.stateStack[idx], ++idx);
      }
      if (s2 != null) 
      {
          StatePrinter.printState(s2, idx+1);
      }
  }

  /* This method does a depth-first search up to the depth of toLevel. */
  public final void run() {
    TLCState curState = null;

    try {
      while (this.stopCode == 0) {
	// Choose a random initial state and compute its successors:
	int index = this.getInit();
	if (index == -1) {
	  this.tlc.setStop(1);
	  synchronized(this.tlc) {
	    this.tlc.setDone();
	    this.tlc.notifyAll();
	  }
	  return;
	}
	
	curState = this.theInitStates[index];
	long cfp = this.theInitFPs[index];
	this.stateStack[0] = curState;
	this.fpStack[0] = cfp;
	this.succStateStack[0].reset();
	this.succFPStack[0].reset();
	boolean isLeaf = this.toLevel < 2;
	boolean noLeaf = this.tlc.doNext(curState, cfp, isLeaf,
					 this.astCounts,
					 this.succStateStack[0],
					 this.succFPStack[0]);
	this.moreLevel = this.moreLevel || !noLeaf;
	this.curLevel = 1;

	// Start the depth-first search:
	while (!isLeaf) {
	  index = this.getNext(curState, cfp);
	  if (index == -1) {
	    // No need to explore further from curState. So, backtrack:
	    this.theFPSet.setLeveled(cfp);
	    if (this.curLevel == 1) break;
	    this.curLevel--;
	    curState = this.stateStack[this.curLevel-1];
	    cfp = this.fpStack[this.curLevel-1];
	  }
	  else {
	    curState = this.succStateStack[this.curLevel-1].elementAt(index);
	    cfp = this.succFPStack[this.curLevel-1].elementAt(index);
	    this.stateStack[this.curLevel] = curState;
	    this.fpStack[this.curLevel] = cfp;
	    this.succStateStack[this.curLevel].reset();
	    this.succFPStack[this.curLevel].reset();
	    isLeaf = (this.curLevel >= this.toLevel-1);
	    noLeaf = this.tlc.doNext(curState, cfp, isLeaf,
				     this.astCounts,
				     this.succStateStack[this.curLevel],
				     this.succFPStack[this.curLevel]);
	    this.moreLevel = this.moreLevel || !noLeaf;
    	    this.curLevel++;
	  }
	}
      }
    }
    catch (Throwable e) {
      // Something bad happened. Quit...
      // Assert.printStack(e);
      this.tlc.setStop(2);
      synchronized(this.tlc) {
	if (this.tlc.setErrState(curState, null, true)) {
          MP.printError(EC.GENERAL, e);  // LL changed call 7 April 2012
	}
	this.tlc.setDone();
	this.tlc.notifyAll();
      }
      return;
    }
  }

}
