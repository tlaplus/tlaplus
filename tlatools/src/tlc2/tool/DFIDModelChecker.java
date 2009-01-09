// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

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
import tlc2.tool.liveness.LiveException;
import tlc2.util.FileUtil;
import tlc2.util.IdThread;
import tlc2.util.LongVec;
import tlc2.util.ObjLongTable;
import util.Assert;
import util.UniqueString;

public class DFIDModelChecker {
  /* A TLA+ Model checker using depth-first iterative deepening */

  /* Constructors  */
  public DFIDModelChecker(String specFile, String configFile, String dumpFile,
			  boolean deadlock, String fromChkpt)
  throws EvalException, IOException {
    this(specFile, configFile, dumpFile, deadlock, fromChkpt, true);
  }
  
  public DFIDModelChecker(String specFile, String configFile, String dumpFile,
			  boolean deadlock, String fromChkpt, boolean preprocess)
  throws EvalException, IOException {
    int lastSep = specFile.lastIndexOf(File.separatorChar);
    String specDir = (lastSep == -1) ? "" : specFile.substring(0, lastSep+1);
    specFile = specFile.substring(lastSep+1);
    this.tool = new Tool(specDir, specFile, configFile);
    this.tool.init(preprocess);
    this.numOfGenStates = 0;
    this.errState = null;
    this.done = false;
    this.keepCallStack = false;
    this.checkDeadlock = deadlock;
    this.checkLiveness = !this.tool.livenessIsTrue();
    this.fromChkpt = fromChkpt;
    this.metadir = makeMetaDir(specDir, fromChkpt);
    this.theInitStates = null;
    this.theInitFPs = null;
    this.theFPSet = new MemFPIntSet();                   // init the state set
    this.theFPSet.init(TLCGlobals.getNumWorkers(), this.metadir, specFile);
    this.impliedInits = this.tool.getImpliedInits();     // implied-inits to be checked
    this.invariants = this.tool.getInvariants();         // invariants to be checked
    this.impliedActions = this.tool.getImpliedActions(); // implied-actions to be checked
    this.actions = this.tool.getActions();               // the subactions
    // Initialize dumpFile:
    if (dumpFile != null) {
      this.allStateWriter = new StateWriter(dumpFile);
    }
    this.lastChkpt = System.currentTimeMillis();
  }

  /* Fields  */
  private long numOfGenStates = 0;
  private TLCState predErrState;
  private TLCState errState;          // set to the error state
  private boolean done;                   
  private boolean keepCallStack;      // record call stack?
  private boolean checkDeadlock;      // check deadlock?
  private boolean checkLiveness;      // check liveness?  
  private String fromChkpt;           // recover from this checkpoint
  public String metadir;              // where metadata reside
  public Tool tool;
  public TLCState[] theInitStates;    // the set of initial states
  public long[] theInitFPs;           //  ... and their fps  
  public FPIntSet theFPSet;           // the set of reachable states
  public Action[] invariants;         // the invariants to be checked
  public Action[] impliedActions;     // the implied-actions to be checked
  public Action[] impliedInits;       // the implied-inits to be checked  
  public Action[] actions;            // the subactions
  private StateWriter allStateWriter; // the dump of all states
  private DFIDWorker[] workers;       // the workers
  private long lastChkpt;             // last checkpoint time

  /**
   * This method does model checking on a TLA+ spec. All the visited
   * states are stored in the variable theFPSet.
   */
  public void modelCheck() throws FileNotFoundException, Exception {
    // Initialization for liveness checking:
    if (this.checkLiveness) {
      LiveCheck.init(this.tool, this.actions, this.metadir);
    }

    boolean recovered = this.recover();
    try {
      if (!this.checkAssumptions()) return;
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
	System.err.println("The error occurred when TLC was evaluating the nested" +
			   "\nexpressions at the following positions:");
	this.tool.printCallStack();
      }
      this.printSummary(false);
      this.cleanup(false);
      return;
    }

    if (recovered) {
      System.err.println("Finished computing initial states: " + this.numOfGenStates +
			 " states generated.\nBecause TLC recovers from a previous" +
			 " checkpoint, only " + this.theInitStates.length +
			 " of them require further exploration.");
    }
    else {
      System.err.println("Finished computing initial states: " + this.numOfGenStates +
			 " states generated, with " + this.theInitStates.length +
			 " of them distinct.");
    }

    // Return if there is no next state predicate:
    if (this.actions.length == 0) {
      this.reportSuccess();
      this.printSummary(true);
      this.cleanup(true);
      return;
    }

    boolean success = false;
    try {
      boolean terminated = false;
      for (int level = 2; level <= TLCGlobals.DFIDMax; level++) {
	// If terminated is true, stop:
	if (terminated) {
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
	      this.doNext(this.predErrState,
			  this.predErrState.fingerPrint(),
			  true,
			  new ObjLongTable(10),
			  new StateVec(1),
			  new LongVec());
	    }
	    catch (Throwable e) {
	      System.err.println("The error occurred when TLC was evaluating the nested\n" +
				 "expressions at the following positions:");
	      this.tool.printCallStack();
	    }
	  }
	  break;
	}

	// Start working on this level:
	System.out.println("Starting level " + level + ": " + this.stats());
	FPIntSet.incLevel();
	success = this.runTLC(level);
	if (!success) return;

	// Check if we should stop at this level:
	for (int i = 0; i < this.workers.length; i++) {
	  if (this.workers[i].isTerminated()) {
	    terminated = true;
	    break;
	  }
	}
	boolean moreLevel = false;
	for (int i = 0; i < this.workers.length; i++) {
	  if (this.workers[i].hasMoreLevel()) {
	    moreLevel = true;
	    break;
	  }
	}
	terminated = terminated || !moreLevel;
      }
    }
    catch (Exception e) {
      // Assert.printStack(e);
      success = false;
      if (!(e instanceof LiveException)) {
	System.err.println("Error: " + e.getMessage());
      }
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

  /* Compute the set of initial states.  */
  private final boolean doInit() throws Throwable {
    TLCState curState = null;
    try {
      // Generate the initial states:
      StateVec states = this.tool.getInitStates();
      this.numOfGenStates = states.size();
      this.theInitStates = new TLCState[(int)this.numOfGenStates];
      this.theInitFPs = new long[(int)this.numOfGenStates];
      int idx = 0;
      for (int i = 0; i < this.numOfGenStates; i++) {
	curState = states.elementAt(i);
	// Check if the state is a legal state
	if (!this.tool.isGoodState(curState)) {
	  System.err.println("Error: State is not completely specified by the " +
			     "initial predicate:");
	  System.err.println(curState.toString());
	  return false;
	}
	boolean inModel = this.tool.isInModel(curState);
	int status = FPIntSet.NEW;
	if (inModel) {
	  long fp = curState.fingerPrint();
	  status = this.theFPSet.setStatus(fp, FPIntSet.NEW);
	  if (status == FPIntSet.NEW) {
	    this.theInitStates[idx] = curState;
	    this.theInitFPs[idx++] = fp;

	    // Write out the state if asked
	    if (this.allStateWriter != null) {
	      this.allStateWriter.writeState(curState);
	    }
	    
	    // build behavior graph for liveness checking
	    if (this.checkLiveness) {
	      LiveCheck.addInitState(curState, fp);
	    }
	  }
	}
	// Check properties of the state:
	if (status == FPIntSet.NEW) {
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

      // Set up the initial pairs correctly:
      if (idx < this.numOfGenStates) {
	TLCState[] stateTemp = new TLCState[idx];
	long[] fpTemp = new long[idx];
	System.arraycopy(this.theInitStates, 0, stateTemp, 0, idx);
	System.arraycopy(this.theInitFPs, 0, fpTemp, 0, idx);
	this.theInitStates = stateTemp;
	this.theInitFPs = fpTemp;
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
   * Compute the set of the next states.  For each next state, check
   * if it is a valid state, if the invariants are satisfied, and if
   * it satisfies the constraints. It also adds the states that have
   * not been done in nextStates.  Return true if it finds a leaf
   * successor of curState.
   */
  public final boolean doNext(TLCState curState,
			      long cfp,
			      boolean isLeaf,
			      ObjLongTable counts,
			      StateVec states,
			      LongVec fps)
  throws Throwable {
    boolean deadLocked = true;
    TLCState succState = null;
    StateVec liveNextStates = null;
    LongVec liveNextFPs = null;

    if (this.checkLiveness && isLeaf) {
      liveNextStates = new StateVec(2);
      liveNextFPs = new LongVec(2);
    }
    
    try {
      int k = 0;
      boolean allSuccDone = true;
      boolean allSuccNonLeaf = true;
      for (int i = 0; i < this.actions.length; i++) {
	StateVec nextStates = this.tool.getNextStates(this.actions[i], curState);
	int sz = nextStates.size();
        this.incNumOfGenStates(sz);
	deadLocked = deadLocked && (sz == 0);

	for (int j = 0; j < sz; j++) {
	  succState = nextStates.elementAt(j);
	  // Check if the state is a legal state.
	  if (!this.tool.isGoodState(succState)) {
	    if (this.setErrState(curState, succState, false)) {
	      System.err.println("Error: Successor state is not completely specified by the" +
				 " next-state action.\nThe behavior up to this point is:");
	      this.printTrace(curState, succState);
	      synchronized(this) { this.notify(); }
	    }
	    return allSuccNonLeaf;
	  }
	  
	  if (TLCGlobals.coverageInterval >= 0) {
	    ((TLCStateMutSource)succState).addCounts(counts);
	  }
	  
	  boolean inModel = (this.tool.isInModel(succState) &&
			     this.tool.isInActions(curState, succState));
	  int status = FPIntSet.NEW;
	  if (inModel) {
	    long fp = succState.fingerPrint();
	    status = this.theFPSet.setStatus(fp, FPIntSet.NEW);
	    allSuccDone = allSuccDone && FPIntSet.isDone(status);
	    allSuccNonLeaf = allSuccNonLeaf && !FPIntSet.isLeaf(status);
	    
	    // Write out the state when new and asked:
	    if (status == FPIntSet.NEW && this.allStateWriter != null) {
	      this.allStateWriter.writeState(succState);
	    }

	    // Remember succState if it has not been completed at this level:
	    if (!FPIntSet.isCompleted(status)) {
	      states.addElement(succState);
	      fps.addElement(fp);
	    }

	    // For liveness checking:
	    if (this.checkLiveness && isLeaf) {
	      liveNextStates.addElement(succState);
	      liveNextFPs.addElement(fp);
	    }
	  }

	  // Check if the state violates any invariant:
	  if (status == FPIntSet.NEW) {
	    try {
	      int len = this.invariants.length;
	      for (k = 0; k < len; k++) {
		if (!tool.isValid(this.invariants[k], succState)) {
		  // We get here because of invariant violation:
		  synchronized(this) {
		    if (TLCGlobals.continuation) {
		      System.err.println("Error: Invariant " + this.tool.getInvNames()[k] +
					 " is violated. The behavior up to this point is:");
		      this.printTrace(curState, succState);
		      break;
		    }
		    else {
		      if (this.setErrState(curState, succState, false)) {
			System.err.println("Error: Invariant " + this.tool.getInvNames()[k] +
					   " is violated. The behavior up to this point is:");
			this.printTrace(curState, succState);
			this.notify();
		      }
		      return allSuccNonLeaf;
		    }
		  }
		}
	      }
	      if (k < len) continue;
	    }
	    catch (Exception e) {
	      if (this.setErrState(curState, succState, true)) {
		System.err.println("Error: Evaluating invariant " + this.tool.getInvNames()[k] +
				   " failed. The behavior up to this point is:");
		this.printTrace(curState, succState);
		this.notify();
	      }
	      return allSuccNonLeaf;
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
		    this.printTrace(curState, succState);
		    break;
		  }
		  else {
		    if (this.setErrState(curState, succState, false)) {
		      System.err.println("Error: Action property " + this.tool.getImpliedActNames()[k] +
					 " is violated. The behavior up to this point is:");
		      this.printTrace(curState, succState);
		      this.notify();
		    }
		    return allSuccNonLeaf;
		  }
		}
	      }
	    }
	    if (k < len) continue;
	  }
	  catch (Exception e) {
	    if (this.setErrState(curState, succState, true)) {
	      System.err.println("Error: Evaluating action property " + this.tool.getImpliedActNames()[k] +
				 " failed. The behavior up to this point is:");
	      this.printTrace(curState, succState);
	      this.notify();
	    }
	    return allSuccNonLeaf;
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
	    this.printTrace(curState, null);
	    this.notify();
	  }
	}
	return allSuccNonLeaf;
      }

      // Finally, add curState into the behavior graph for liveness checking:
      if (this.checkLiveness && isLeaf) {
	// Add a stuttering step for curState:
	long curStateFP = curState.fingerPrint();
	liveNextStates.addElement(curState);
	liveNextFPs.addElement(curStateFP);
	// Add curState to the behavior graph:
	LiveCheck.addNextState(curState, curStateFP, liveNextStates, liveNextFPs);
      }

      // We set curState DONE if
      //    o all of its children is already DONE, or
      //    o it is a leaf state and none of its children is NEW.
      // Otherwise, set curState to NONELEAF.
      if (allSuccDone || (isLeaf && allSuccNonLeaf)) {
	this.theFPSet.setStatus(cfp, FPIntSet.DONE);
      }
      return allSuccNonLeaf;
    }
    catch (Throwable e) {
      // Assert.printStack(e);
      boolean keep = ((e instanceof StackOverflowError) ||
		      (e instanceof OutOfMemoryError));
      synchronized(this) {
	if (this.setErrState(curState, succState, !keep)) {
	  if (e instanceof StackOverflowError) {
	    System.err.println("Error: This was a Java StackOverflowError. It was probably the\n" +
			       "result of an incorrect recursive function definition that caused\n" +
			       "TLC to enter an infinite loop when trying to compute the function\n" +
			       "or its application to an element in its putative domain.");
	  }
	  else if (e instanceof OutOfMemoryError) {
	    System.err.println("Error: Java ran out of memory.  Running Java with a larger memory\n" +
			       "allocation pool (heap) may fix this.  But it won't help if some\n" +
			       "state has an enormous number of successor states, or if TLC must\n" +
			       "compute the value of a huge set.");
	  }
	  else {
	    System.err.println("Error: " + e.getMessage());
	  }
	  System.err.println("The behavior up to this point is:");
	  this.printTrace(curState, succState);
	  this.notifyAll();
	}
      }
      throw e;
    }
  }

  private final void printTrace(TLCState s1, TLCState s2) {
    this.workers[IdThread.GetId()].printTrace(s1, s2);
  }
  
  /* Must be protected by lock */
  public final boolean setErrState(TLCState curState, TLCState state,
				   boolean keep) {
    if (!TLCGlobals.continuation && this.done) return false;
    this.predErrState = curState;
    this.errState = (state == null) ? curState : state;
    this.done = true;
    this.keepCallStack = keep;
    this.setStop(2);
    return true;
  }

  public final void setDone() { this.done = true; }

  private final synchronized void incNumOfGenStates(int n) {
    this.numOfGenStates += n;
  }

  private static long nextLiveCheck = 1000;
  
  /**
   * There are several things to do:
   * Check liveness: check liveness properties on the partial state graph.
   * Checkpoint: checkpoint three data structures: the state set, the
   *             state queue, and the state trace.
   */
  public final boolean doPeriodicWork() throws Exception {
    synchronized(this.theFPSet) {
      // Run liveness checking, if needed:
      long stateNum = this.theFPSet.size();
      boolean doCheck = this.checkLiveness && (stateNum >= nextLiveCheck);
      if (doCheck) {
	System.out.println("--Checking temporal properties for the current state space...");
	if (!LiveCheck.check()) return false;
	nextLiveCheck = (stateNum < 600000) ? stateNum*2 : stateNum+200000;
      }

      // Checkpoint:
      System.out.print("--Checkpointing of run " + this.metadir + " compl");      
      // start checkpointing:
      this.theFPSet.beginChkpt();
      if (this.checkLiveness) LiveCheck.beginChkpt();
      UniqueString.internTbl.beginChkpt(this.metadir);      

      // Commit checkpoint:
      this.theFPSet.commitChkpt();
      if (this.checkLiveness) LiveCheck.commitChkpt();      
      UniqueString.internTbl.commitChkpt(this.metadir);
      System.out.println("eted.");      
    }
    return true;
  }

  public final boolean recover() throws IOException {
    boolean recovered = false;
    if (this.fromChkpt != null) {
      // We recover from previous checkpoint.
      System.out.println("-- Starting recovery from checkpoint " + this.fromChkpt);
      this.theFPSet.recover();
      if (this.checkLiveness) LiveCheck.recover();
      System.out.println("-- Recovery completed. " + this.recoveryStats());
      recovered = true;
      this.numOfGenStates = this.theFPSet.size();
    }
    return recovered;
  }

  private final String recoveryStats() {
    return this.theFPSet.size() + " states examined.";
  }
  
  private final String stats() {
    return (this.numOfGenStates + " states generated, " +
	    this.theFPSet.size() + " distinct states found.");
  }

  private final void cleanup(boolean success) throws IOException {
    this.theFPSet.close();
    if (this.checkLiveness) LiveCheck.close();
    if (this.allStateWriter != null) this.allStateWriter.close();
    FileUtil.deleteDir(new File(this.metadir), success);
  }
  
  public final void printSummary(boolean success) throws IOException {
    this.reportCoverage();
    System.out.println(this.stats());
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
   **/
  public static String makeMetaDir(String specDir, String fromChkpt) {
    if (fromChkpt != null) return fromChkpt;
    if (TLCGlobals.metaDir != null) return TLCGlobals.metaDir;

    // If not given, use the directory specDir/metaRoot:
    String metadir = specDir + TLCGlobals.metaRoot + File.separator;
    SimpleDateFormat sdf = new SimpleDateFormat("yy-MM-dd-HH-mm-ss");
    metadir += sdf.format(new Date());
    File filedir = new File(metadir);
    if (filedir.exists()) {
      Assert.fail("Error: TLC writes its files to a directory whose name is" +
		  " the current time.\nThis directory should be " + metadir +
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

  /**
   * Create the partial state space up to the given depth. Return
   * true if one of the workers wants to terminate.  A worker
   * wants to terminate if it either decides the complete state
   * space is explored or detects an error in the spec.
   */
  public final boolean runTLC(int toLevel) throws Exception {
    // Start all the workers:
    this.workers = new DFIDWorker[TLCGlobals.getNumWorkers()];
    for (int i = 0; i < this.workers.length; i++) {
      this.workers[i] = new DFIDWorker(i, toLevel, this);
      this.workers[i].start();
    }

    // Check progress periodically:
    boolean success = false;
    int count = TLCGlobals.coverageInterval/TLCGlobals.progressInterval;
    this.done = false;
    synchronized(this) { this.wait(30000); }
    while (true) {
      long now = System.currentTimeMillis();
      if (now - this.lastChkpt >= TLCGlobals.chkptDuration) {
	if (!this.doPeriodicWork()) { return false; }
	this.lastChkpt = now;
      }
      synchronized(this) {
	if (!this.done) {
	  System.out.println("Progress: " + this.stats());
	  if (count == 0) {
	    this.reportCoverage();	      
	    count = TLCGlobals.coverageInterval/TLCGlobals.progressInterval;
	  }
	  else {
	    count--;
	  }
	  this.wait(TLCGlobals.progressInterval);
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

  public final void setStop(int code) {
    for (int i = 0; i < this.workers.length; i++) {
      this.workers[i].setStop(code);
    }
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
