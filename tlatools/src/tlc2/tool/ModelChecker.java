// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed  4 Jul 2007 at 17:46:34 PST by lamport  
//      modified on Fri Jan 18 11:33:51 PST 2002 by yuanyu   

package tlc2.tool;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.text.SimpleDateFormat;
import java.util.Date;

import tla2sany.semantic.ExprNode;
import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.tool.liveness.LiveCheck;
import tlc2.util.FileUtil;
import tlc2.util.LongVec;
import tlc2.util.ObjLongTable;
import tlc2.value.Value;
import util.Assert;
import util.UniqueString;

public class ModelChecker {
  /* A TLA+ Model checker */

  /* Constructors  */
  public ModelChecker(String specFile, String configFile, String dumpFile,
		      boolean deadlock, String fromChkpt)
  throws EvalException, IOException {
    int lastSep = specFile.lastIndexOf(File.separatorChar);
    String specDir = (lastSep == -1) ? "" : specFile.substring(0, lastSep+1);
    specFile = specFile.substring(lastSep+1);
    this.tool = new Tool(specDir, specFile, configFile);
    this.tool.init(true);
    this.numOfGenStates = 0;
    this.errState = null;
    this.done = false;
    this.keepCallStack = false;
    this.checkDeadlock = deadlock;
    this.checkLiveness = !this.tool.livenessIsTrue();
    this.fromChkpt = fromChkpt;
    this.metadir = makeMetaDir(specDir, fromChkpt);
    this.theStateQueue = new DiskStateQueue(this.metadir);
    // this.theStateQueue = new MemStateQueue(this.metadir);
    this.theFPSet = new MultiFPSet(1);
    // this.theFPSet = new DiskFPSet(-1);
    // this.theFPSet = new MemFPSet();
    // this.theFPSet = new MemFPSet1();
    // this.theFPSet = new MemFPSet2();
    this.theFPSet.init(TLCGlobals.getNumWorkers(), this.metadir, specFile);
    this.impliedInits = this.tool.getImpliedInits();     // implied-inits to be checked
    this.invariants = this.tool.getInvariants();         // invariants to be checked
    this.impliedActions = this.tool.getImpliedActions(); // implied-actions to be checked
    this.actions = this.tool.getActions();               // the subactions
    // Initialize dumpFile:
    if (dumpFile != null) {
      this.allStateWriter = new StateWriter(dumpFile);
    }
    // Finally, initialize the trace file:
    this.trace = new TLCTrace(this.metadir, specFile, this.tool);
    this.lastChkpt = System.currentTimeMillis();
    // Initialize all the workers:
    this.workers = new Worker[TLCGlobals.getNumWorkers()];
    for (int i = 0; i < this.workers.length; i++) {
      this.workers[i] = new Worker(i, this);
    }
  }

  public ModelChecker(String specFile, String configFile, boolean deadlock)
  throws EvalException, IOException {
    int lastSep = specFile.lastIndexOf(File.separatorChar);
    String specDir = (lastSep == -1) ? "" : specFile.substring(0, lastSep+1);
    specFile = specFile.substring(lastSep+1);
    this.tool = new Tool(specDir, specFile, configFile);
    this.tool.init(false);
    this.numOfGenStates = 0;
    this.errState = null;
    this.done = false;
    this.keepCallStack = false;
    this.checkDeadlock = deadlock;
    this.checkLiveness = !this.tool.livenessIsTrue();
    this.impliedInits = this.tool.getImpliedInits();     // implied-inits to be checked
    this.invariants = this.tool.getInvariants();         // invariants to be checked
    this.impliedActions = this.tool.getImpliedActions(); // implied-actions to be checked
    this.actions = this.tool.getActions();               // the subactions
    this.lastChkpt = System.currentTimeMillis();
    // Initialize all the workers:
    this.workers = new Worker[TLCGlobals.getNumWorkers()];
    for (int i = 0; i < this.workers.length; i++) {
      this.workers[i] = new Worker(i, this);
    }
  }

  /* Fields  */
  private long numOfGenStates = 0;
  private TLCState predErrState;
  private TLCState errState;              // set to the error state
  private boolean done;                   
  private boolean keepCallStack;          // record call stack?
  private boolean checkDeadlock;          // check deadlock?
  private boolean checkLiveness;          // check liveness?  
  private String fromChkpt;               // recover from this checkpoint
  public String metadir;                  // where metadata reside
  public Tool tool;
  public FPSet theFPSet;                  // the set of reachable states
  public StateQueue theStateQueue;        // the state queue
  public Action[] invariants;             // the invariants to be checked
  public Action[] impliedActions;         // the implied-actions to be checked
  public Action[] impliedInits;           // the implied-inits to be checked  
  public Action[] actions;                // the subactions
  public TLCTrace trace;                  // the trace file
  private StateWriter allStateWriter;     // the dump of all states
  private Worker[] workers;               // the workers
  private long lastChkpt;                 // last checkpoint time

  /**
   * This method does model checking on a TLA+ spec. All the visited
   * states are stored in the variable theFPSet. All the states whose
   * next states have not been explored are stored in the variable
   * theStateQueue.
   */
  public void modelCheck() throws FileNotFoundException, Exception {
    // Initialization for liveness checking:
    if (this.checkLiveness) {
      LiveCheck.init(this.tool, this.actions, this.metadir);
    }

    boolean recovered = this.recover();
    if (!recovered) {
      // We start from scratch. Initialize the state queue and the
      // state set to contain all the initial states.
      if (!this.checkAssumptions()) return;
      try {
	if (!this.doInit()) return;
      }
      catch (Throwable e) {
	// Initial state computation fails with an exception:
	System.err.println("Error: " + e.getMessage());
	if (this.errState != null) {
	  System.err.println("While working on the initial state:");
	  System.err.println(this.errState);
	}
	// Replay the error with the error stack recorded:
	this.tool.setCallStack();
	try {
	  this.numOfGenStates = 0;
	  this.doInit();
	}
	catch (Throwable e1) {
	  // Assert.printStack(e);
	  System.err.println("\nThe error occurred when TLC was evaluating the nested" +
			     "\nexpressions at the following positions:");
	  this.tool.printCallStack();
	}
	this.printSummary(false);
	this.cleanup(false);
	return;
      }
      
      if (this.numOfGenStates == this.theFPSet.size()) {
	String plural = (this.numOfGenStates == 1) ? "" : "s";	
        System.err.println("Finished computing initial states: " + this.numOfGenStates +
			   " distinct state" + plural + " generated.");
      }
      else {
        System.err.println("Finished computing initial states: " + this.numOfGenStates +
			   " states generated, with " + this.theFPSet.size() +
			   " of them distinct.");
      }
    }

    // Finished if there is no next state predicate:
    if (this.actions.length == 0) {
      this.reportSuccess();
      this.printSummary(true);
      this.cleanup(true);
      return;
    }

    boolean success = false;
    try {
      success = this.runTLC(Integer.MAX_VALUE);
      if (!success) return;

      if (this.errState == null) {
	// Always check liveness properties at the end:
	if (this.checkLiveness) {
	  System.out.println("--Checking temporal properties for the complete state space...");
	  System.out.flush();	  
	  success = LiveCheck.check();
	  if (!success) return;
	}
	
	// We get here because the checking has been completed.
	success = true;
	this.reportSuccess();
      }
      else if (this.keepCallStack) {
	// Replay the error with the error stack recorded:
	this.tool.setCallStack();
	try {
	  this.doNext(this.predErrState, new ObjLongTable(10));
	}
	catch (Throwable e) {
	  // Assert.printStack(e);
	  System.err.println("\nThe error occurred when TLC was evaluating the nested" +
			     "\nexpressions at the following positions:");
	  this.tool.printCallStack();
	}
      }
    }
    catch (Exception e) {
      // Assert.printStack(e);
      success = false;
      System.err.println("Error: " + e.getMessage());
    }
    finally {
      this.printSummary(success);
      this.cleanup(success);
    }
  }

  /* Check the assumptions.  */
  public final boolean checkAssumptions() {
    ExprNode[] assumps = this.tool.getAssumptions();
    for (int i = 0; i < assumps.length; i++) {
      try {
	if (!this.tool.isValid(assumps[i])) {
	  System.err.println("Error: Assumption " + assumps[i] + " is false.");
	  return false;
	}
      }
      catch (Exception e) {
	// Assert.printStack(e);
	System.err.println("Error: Evaluating assumption " + assumps[i] + " failed.");
	System.err.println(e.getMessage());
	return false;
      }
    }
    return true;
  }

  public final boolean doInit() throws Throwable {
    TLCState curState = null;

    try {
      // Generate the initial states:
      StateVec theInitStates = this.tool.getInitStates();
      this.numOfGenStates = theInitStates.size();
      for (int i = 0; i < theInitStates.size(); i++) {
	curState = theInitStates.elementAt(i);
	// Check if the state is a legal state
	if (!this.tool.isGoodState(curState)) {
	  System.err.println("Error: State was not completely specified by the " +
			     "initial predicate:");
	  System.err.println(curState.toString());
	  return false;
	}
	boolean inModel = this.tool.isInModel(curState);
	boolean seen = false;
	if (inModel) {
	  long fp = curState.fingerPrint();
	  seen = this.theFPSet.put(fp);
	  if (!seen) {
	    if (this.allStateWriter != null) {
	      this.allStateWriter.writeState(curState);
	    }
	    curState.uid = this.trace.writeState(1, fp);
	    this.theStateQueue.enqueue(curState);

	    // build behavior graph for liveness checking
	    if (this.checkLiveness) {
	      LiveCheck.addInitState(curState, fp);
	    }
	  }
	}
	// Check properties of the state:
	if (!seen) {
	  for (int j = 0; j < this.invariants.length; j++) {
	    if (!this.tool.isValid(this.invariants[j], curState)) {
	      // We get here because of invariant violation:
	      System.err.println("Error: Invariant " + this.tool.getInvNames()[j] +
				 " is violated by the initial state:");
	      System.err.println(curState.toString());
	      if (!TLCGlobals.continuation) return false;
	    }
	  }
	  for (int j = 0; j < this.impliedInits.length; j++) {
	    if (!this.tool.isValid(this.impliedInits[j], curState)) {
	      // We get here because of implied-inits violation:
	      System.err.println("Error: Property " + this.tool.getImpliedInitNames()[j] +
				 " is violated by the initial state:");
	      System.err.println(curState.toString());
	      return false;
	    }
	  }
	}
      }
    }
    catch (Throwable e) {
      // Assert.printStack(e);
      if (e instanceof OutOfMemoryError) {
	System.err.println("OutOfMemoryError: There are probably too many initial states.");
	return false;
      }
      this.errState = curState;
      throw e;
    }
    return true;
  }

  /**
   * Compute the set of the next states.  For each next state, check that
   * it is a valid state, check that the invariants are satisfied, check
   * that it satisfies the constraints, and enqueue it in the state queue.
   * Return true if the model checking should stop.
   */
  public final boolean doNext(TLCState curState, ObjLongTable counts)
  throws Throwable {
    boolean deadLocked = true;
    TLCState succState = null;
    Action curAction = null;
    StateVec liveNextStates = null;
    LongVec liveNextFPs = null;

    if (this.checkLiveness) {
      liveNextStates = new StateVec(2);
      liveNextFPs = new LongVec(2);
    }

    try {
      int k = 0;
      for (int i = 0; i < this.actions.length; i++) {
	StateVec nextStates = this.tool.getNextStates(this.actions[i], curState);
	int sz = nextStates.size();
        this.incNumOfGenStates(sz);
	deadLocked = deadLocked && (sz == 0);

	for (int j = 0; j < sz; j++) {
	  succState = nextStates.elementAt(j);
	  // Check if succState is a legal state.
	  if (!this.tool.isGoodState(succState)) {
	    if (this.setErrState(curState, succState, false)) {
	      System.err.println("Error: Successor state is not completely specified by the" +
				 " next-state action.\nThe behavior up to this point is:");
	      this.trace.printTrace(curState.uid, curState, succState);
	      this.theStateQueue.finishAll();
	      synchronized(this) { this.notify(); }
	    }
	    return true;
	  }
	  if (TLCGlobals.coverageInterval >= 0) {
	    ((TLCStateMutSource)succState).addCounts(counts);
	  }
	  
	  boolean inModel = (this.tool.isInModel(succState) &&
			     this.tool.isInActions(curState, succState));
	  boolean seen = false;
	  if (inModel) {
	    long fp = succState.fingerPrint();
	    seen = this.theFPSet.put(fp);
	    if (!seen) {
	      // Write out succState when needed:
	      if (this.allStateWriter != null) {
		this.allStateWriter.writeState(succState);
	      }
	      // Enqueue succState only if it satisfies the model constraints:
	      long loc = this.trace.writeState(curState.uid, fp);
	      succState.uid = loc;
	      this.theStateQueue.sEnqueue(succState);
	    }
	    // For liveness checking:
	    if (this.checkLiveness) {
	      liveNextStates.addElement(succState);
	      liveNextFPs.addElement(fp);
	    }
	  }
	  // Check if succState violates any invariant:
	  if (!seen) {
	    try {
	      int len = this.invariants.length;
	      for (k = 0; k < len; k++) {
		if (!tool.isValid(this.invariants[k], succState)) {
		  // We get here because of invariant violation:
		  synchronized(this) {
		    if (TLCGlobals.continuation) {
		      System.err.println("Error: Invariant " + this.tool.getInvNames()[k] +
					 " is violated. The behavior up to this point is:");
		      this.trace.printTrace(curState.uid, curState, succState);
		      break;
		    }
		    else {
		      if (this.setErrState(curState, succState, false)) {
			System.err.println("Error: Invariant " + this.tool.getInvNames()[k] +
					   " is violated. The behavior up to this point is:");
			this.trace.printTrace(curState.uid, curState, succState);
			this.theStateQueue.finishAll();
			this.notify();
		      }
		      return true;
		    }
		  }
		}
	      }
	      if (k < len) continue;
	    }
	    catch (Exception e) {
	      if (this.setErrState(curState, succState, true)) {
		System.err.println("Error: Evaluating invariant " + this.tool.getInvNames()[k] +
				   " failed.");
		System.err.println(e.getMessage());
		System.err.println("\nThe behavior up to this point is:");
		this.trace.printTrace(curState.uid, curState, succState);
		this.theStateQueue.finishAll();
		this.notify();
	      }
	      throw e;
	    }
	  }
	  // Check if the state violates any implied action.  We need to do it
	  // even if succState is not new.
	  try {
	    int len = this.impliedActions.length;
	    for (k = 0; k < len; k++) {
	      if (!tool.isValid(this.impliedActions[k], curState, succState)) {
		// We get here because of implied-action violation:
		synchronized(this) {
		  if (TLCGlobals.continuation) {
		    System.err.println("Error: Action property " + this.tool.getImpliedActNames()[k] +
				       " is violated. The behavior up to this point is:");
		    this.trace.printTrace(curState.uid, curState, succState);
		    break;
		  }
		  else {
		    if (this.setErrState(curState, succState, false)) {
		      System.err.println("Error: Action property " + this.tool.getImpliedActNames()[k] +
					 " is violated. The behavior up to this point is:");
		      this.trace.printTrace(curState.uid, curState, succState);
		      this.theStateQueue.finishAll();
		      this.notify();
		    }
		    return true;
		  }
		}
	      }
	    }
	    if (k < len) continue;
	  }
	  catch (Exception e) {
	    if (this.setErrState(curState, succState, true)) {
	      System.err.println("Error: Evaluating action property " + this.tool.getImpliedActNames()[k] +
				 " failed.");
	      System.err.println(e.getMessage());
	      System.err.println("\nThe behavior up to this point is:");
	      this.trace.printTrace(curState.uid, curState, succState);
	      this.theStateQueue.finishAll();
	      this.notify();
	    }
	    throw e;
	  }
	}
	// Must set state to null!!!
	succState = null;
      }
      // Check for deadlock:
      if (deadLocked && this.checkDeadlock) {
	synchronized(this) {
	  if (this.setErrState(curState, null, false)) {
	    System.err.println("Error: deadlock reached. The behavior up to this point is:");
	    this.trace.printTrace(curState.uid, curState, null);
	    this.theStateQueue.finishAll();
	    this.notify();
	  }
	}
	return true;
      }
      // Finally, add curState into the behavior graph for liveness checking:
      if (this.checkLiveness) {
	// Add the stuttering step:
	long curStateFP = curState.fingerPrint();
	liveNextStates.addElement(curState);
	liveNextFPs.addElement(curStateFP);
	LiveCheck.addNextState(curState, curStateFP, liveNextStates, liveNextFPs);
      }
      return false;
    }
    catch (Throwable e) {
      // Assert.printStack(e);
      boolean keep = ((e instanceof StackOverflowError) ||
		      (e instanceof OutOfMemoryError));
      synchronized(this) {
	if (this.setErrState(curState, succState, !keep)) {
	  if (e instanceof StackOverflowError) {
	    System.err.println("Error: This was a Java StackOverflowError. It was probably the result\n" +
			       "of an incorrect recursive function definition that caused TLC to enter\n" +
			       "an infinite loop when trying to compute the function or its application\n" +
			       "to an element in its putative domain.");
	  }
	  else if (e instanceof OutOfMemoryError) {
	    System.err.println("Error: Java ran out of memory. Running Java with a larger memory allocation\n" +
			       "pool (heap) may fix this. But it won't help if some state has an enormous\n" +
			       "number of successor states, or if TLC must compute the value of a huge set.\n");
	  }
	  else {
	    System.err.println("Error: " + e.getMessage());
	  }
	  System.err.println("\nThe behavior up to this point is:");
	  this.trace.printTrace(curState.uid, curState, succState);
	  this.theStateQueue.finishAll();
	  this.notify();
	}
      }
      throw e;
    }
  }

  /* Must be protected by lock */
  public final boolean setErrState(TLCState curState, TLCState succState,
				   boolean keep) {
    if (!TLCGlobals.continuation && this.done) return false;
    this.predErrState = curState;
    this.errState = (succState == null) ? curState : succState;
    this.done = true;
    this.keepCallStack = keep;
    return true;
  }

  public final void setDone() { this.done = true; }

  private final synchronized void incNumOfGenStates(int n) {
    this.numOfGenStates += n;
  }

  private static long nextLiveCheck = 10000;
  
  /**
   * Things need to be done here:
   * Check liveness: check liveness properties on the partial state graph.
   * Create checkpoint: checkpoint three data structures: the state set,
   *                    the state queue, and the state trace.
   */
  public final boolean doPeriodicWork() throws Exception {
    if (this.theStateQueue.suspendAll()) {
      // Run liveness checking, if needed:
      long stateNum = this.theFPSet.size();
      boolean doCheck = this.checkLiveness && (stateNum >= nextLiveCheck);
      if (doCheck) {
	System.out.println("--Checking temporal properties for the current state space...");
	if (!LiveCheck.check()) return false;
	nextLiveCheck = (stateNum <= 640000) ? stateNum*2 : stateNum+640000;
      }

      // Checkpoint:
      System.out.print("--Checkpointing of run " + this.metadir + " compl");
      // start checkpointing:
      this.theStateQueue.beginChkpt();
      this.trace.beginChkpt();
      this.theFPSet.beginChkpt();
      this.theStateQueue.resumeAll();
      UniqueString.internTbl.beginChkpt(this.metadir);
      if (this.checkLiveness) LiveCheck.beginChkpt();
      
      // commit checkpoint:
      this.theStateQueue.commitChkpt();
      this.trace.commitChkpt();
      this.theFPSet.commitChkpt();
      UniqueString.internTbl.commitChkpt(this.metadir);
      if (this.checkLiveness) LiveCheck.commitChkpt();      
      System.out.println("eted.");
    }
    return true;
  }

  public final boolean recover() throws IOException {
    boolean recovered = false;
    if (this.fromChkpt != null) {
      // We recover from previous checkpoint.
      System.out.println("--Starting recovery from checkpoint " + this.fromChkpt);
      this.trace.recover();
      this.theStateQueue.recover();
      this.theFPSet.recover();
      if (this.checkLiveness) LiveCheck.recover();
      System.out.println("--Recovery completed. " + this.recoveryStats());
      recovered = true;
      this.numOfGenStates = this.theFPSet.size();
    }
    return recovered;
  }

  private final String recoveryStats() {
    return (this.theFPSet.size() + " states examined. " +
	    this.theStateQueue.size() + " states on queue.");
  }
  
  private final String stats() {
    return (this.numOfGenStates + " states generated, " +
	    this.theFPSet.size() + " distinct states found, " +
	    this.theStateQueue.size() + " states left on queue.");
  }

  private final void cleanup(boolean success) throws IOException {
    this.theFPSet.close();
    this.trace.close();
    if (this.checkLiveness) LiveCheck.close();
    if (this.allStateWriter != null) this.allStateWriter.close();
    FileUtil.deleteDir(new File(this.metadir), success);
  }
  
  public final void printSummary(boolean success) throws IOException {
    this.reportCoverage();
    System.out.println(this.stats());
    if (success) {
      System.out.println("The depth of the complete state graph search is " + 
			 this.trace.getLevel() + ".");
    }
  }

  public final void reportSuccess() throws IOException {
    long d = this.theFPSet.size();
    double prob1 = (d*(this.numOfGenStates-d))/Math.pow(2, 64);
    double prob2 = this.theFPSet.checkFPs();    

    System.out.println("Model checking completed. No error has been found.\n" +
		       "  Estimates of the probability that TLC did not check " +
		       "all reachable states\n  because two distinct states had " +
		       "the same fingerprint:\n" +
		       "    calculated (optimistic):  " + prob1 + "\n" +
		       "    based on the actual fingerprints:  " + prob2);
  }

  private final void reportCoverage() {
    if (TLCGlobals.coverageInterval >= 0) {
      System.out.println("The coverage stats:");
      // First collecting all counts from all workers:
      ObjLongTable counts = this.tool.getPrimedLocs();
      for (int i = 0; i < this.workers.length; i++) {
	ObjLongTable counts1 = this.workers[i].getCounts();
	ObjLongTable.Enumerator keys = counts1.keys();
	Object key;
	while ((key = keys.nextElement()) != null) {
	  String loc = ((SemanticNode)key).getLocation().toString();
	  counts.add(loc, counts1.get(key));
	}
      }
      // Reporting:
      Object[] skeys = counts.sortStringKeys();
      for (int i = 0; i < skeys.length; i++) {
	long val = counts.get(skeys[i]);
	System.out.println("  " + skeys[i] + ": " + val);
      }
    }
  }
  
  /**
   * The metadir is fromChkpt if it is not null. Otherwise, create a
   * new one based on the current time.
   */
  public static String makeMetaDir(String specDir, String fromChkpt) {
    if (fromChkpt != null) return fromChkpt;
    String metadir = TLCGlobals.metaDir;
    if (metadir == null) {
      // If not given, use the directory specDir/metaRoot:
      metadir = specDir + TLCGlobals.metaRoot + File.separator;
    }
    
    SimpleDateFormat sdf = new SimpleDateFormat("yy-MM-dd-HH-mm-ss");
    metadir += sdf.format(new Date());
    File filedir = new File(metadir);
    if (filedir.exists()) {
      Assert.fail("Error: TLC writes its files to a directory whose name is generated" +
		  " from the current time.\nThis directory should be " + metadir +
		  ", but that directory already exists.\n" +
		  "Trying to run TLC again will probably fix this problem.\n");
    }
    else {
      Assert.check(filedir.mkdirs(),
		   "Error: TLC could not make a directory for the disk files" +
		   " it needs to write.\n");
    }
    return metadir;
  }

  public final void setAllValues(int idx, Value val) {
    for (int i = 0; i < this.workers.length; i++) {
      workers[i].setLocalValue(idx, val);
    }
  }

  public final Value getValue(int i, int idx) {
    return workers[i].getLocalValue(idx);
  }

  /**
   * Create the partial state space for given starting state up
   * to the given depth or the number of states.
   */
  public final boolean runTLC(int depth) throws Exception {
    if (depth < 2) return true;
    
    // Start all the workers:
    for (int i = 0; i < this.workers.length; i++) {
      this.workers[i].start();
    }

    // Check progress periodically:
    boolean success = false;
    int count = TLCGlobals.coverageInterval/TLCGlobals.progressInterval;
    synchronized(this) { this.wait(30000); }
    while (true) {
      long now = System.currentTimeMillis();
      if (now - this.lastChkpt >= TLCGlobals.chkptDuration) {
	if (!this.doPeriodicWork()) { return false; }
	this.lastChkpt = now;
      }
      synchronized(this) {
	int level = this.trace.getLevel();
	if (!this.done) {
	  System.out.println("Progress(" + level +"): " + this.stats());
	  if (level > depth) {
	    this.theStateQueue.finishAll();
	    this.done = true;
	  }
	  else {
	    if (count == 0) {
	      this.reportCoverage();	      
	      count = TLCGlobals.coverageInterval/TLCGlobals.progressInterval;
	    }
	    else {
	      count--;
	    }
	    this.wait(TLCGlobals.progressInterval);
	  }
	}
	if (this.done) break;
      }
    }

    // Wait for all the workers to terminate:
    for (int i = 0; i < this.workers.length; i++) {
      this.workers[i].join();
    }
    return true;
  }
  
  final class StateWriter {
    private PrintWriter writer;
    private int stateNum;
    
    StateWriter(String fname) throws IOException {
      FileOutputStream fos = new FileOutputStream(fname);
      this.writer = new PrintWriter(new BufferedOutputStream(fos));
      this.stateNum = 1;
    }

    synchronized final void writeState(TLCState state) {
      this.writer.println("State " + this.stateNum + ":");
      this.writer.println(state.toString());
      this.stateNum++;
    }

    final void close() { this.writer.close(); }
  }

}
