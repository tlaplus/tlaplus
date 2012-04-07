// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:56 PST by lamport
//      modified on Thu Jan 10 11:22:26 PST 2002 by yuanyu

package tlc2.tool;

import java.io.PrintWriter;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.output.StatePrinter;
import tlc2.tool.liveness.LiveCheck1;
import tlc2.tool.liveness.LiveException;
import tlc2.util.ObjLongTable;
import tlc2.util.RandomGenerator;
import util.FileUtil;
import util.FilenameToStream;

public class Simulator implements Cancelable 
{

    /* Constructors  */
    /**
     * SZ Feb 20, 2009: added the possibility to pass the SpecObject, this is compatibility constructor
     * @deprecated use {@link Simulator#Simulator(String, String, String, boolean, int, long, RandomGenerator, long, boolean, FilenameToStream, SpecObj)} instead
     * and pass the <code>null</code> as SpecObj
     */
    public Simulator(String specFile, String configFile, String traceFile, boolean deadlock, int traceDepth,
            long traceNum, RandomGenerator rng, long seed, boolean preprocess, FilenameToStream resolver)
    {
        this(specFile, configFile, traceFile, deadlock, traceDepth, traceNum, rng, seed, preprocess, resolver, null);
    }
    
    // SZ Feb 20, 2009: added the possibility to pass the SpecObject    
    public Simulator(String specFile, String configFile, String traceFile,
		   boolean deadlock, int traceDepth, long traceNum,
		   RandomGenerator rng, long seed, boolean preprocess, FilenameToStream resolver, SpecObj specObj) {
    int lastSep = specFile.lastIndexOf(FileUtil.separatorChar);
    String specDir = (lastSep == -1) ? "" : specFile.substring(0, lastSep+1);
    specFile = specFile.substring(lastSep+1);

    // SZ Feb 24, 2009: setup the user directory
    // SZ Mar 5, 2009: removed it again because of the bug in simulator
    // ToolIO.setUserDir(specDir);
    
    this.tool = new Tool(specDir, specFile, configFile, resolver);

    this.tool.init(preprocess, specObj);   // parse and process the spec

    this.checkDeadlock = deadlock;
    this.checkLiveness = !this.tool.livenessIsTrue();
    this.actions = this.tool.getActions();
    this.invariants = this.tool.getInvariants();
    this.impliedActions = this.tool.getImpliedActions();
    this.numOfGenStates = 0;
    if (traceDepth != -1) {
      this.stateTrace = new TLCState[traceDepth];
//      this.actionTrace = new Action[traceDepth];  // SZ: never read locally
      this.traceDepth = traceDepth;
    }
    else {
      this.stateTrace = new TLCState[0];
//      this.actionTrace = new Action[0];           // SZ: never read locally      
      this.traceDepth = Long.MAX_VALUE;
    }
    this.traceFile = traceFile;
    this.traceNum = traceNum;
    this.rng = rng;
    this.seed = seed;
    this.aril = 0;
    this.astCounts = new ObjLongTable(10);
    // Initialization for liveness checking
    if (this.checkLiveness) {
      LiveCheck1.initSim(this.tool);
    }
  }

  /* Fields */
  private Tool tool;
  private Action[] actions;          // the sub actions
  private Action[] invariants;       // the invariants to be checked
  private Action[] impliedActions;   // the implied-actions to be checked  
  private boolean checkDeadlock;     // check deadlock?
  private boolean checkLiveness;     // check liveness?
  private long numOfGenStates;
  private TLCState[] stateTrace;
  // private Action[] actionTrace;  // SZ: never read locally
  private String traceFile;
  private long traceDepth;
  private long traceNum;
  private RandomGenerator rng;
  private long seed;
  private long aril;
  private ObjLongTable astCounts;
  private boolean isCancelled; // SZ Feb 24, 2009: cancellation added
  
  /*
   * This method does simulation on a TLA+ spec. Its argument specifies
   * the main module of the TLA+ spec.
   */
  public void simulate() throws Exception {
    StateVec theInitStates = null;
    TLCState curState = null;

    if (isCancelled) 
    {
        return;
    }
    // Compute the initial states:
    try {
      theInitStates = this.tool.getInitStates();
      this.numOfGenStates = theInitStates.size();
      for (int i = 0; i < theInitStates.size(); i++) {
	curState = theInitStates.elementAt(i);
	if (this.tool.isGoodState(curState)) {
	  for (int j = 0; j < this.invariants.length; j++) {
	    if (!this.tool.isValid(this.invariants[j], curState)) {
	      // We get here because of invariant violation:
	        MP.printError(EC.TLC_INVARIANT_VIOLATED_INITIAL, new String[]{this.tool.getInvNames()[j], curState.toString()});
	      return;
	    }
	  }
	}
	else {
	    MP.printError(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_INITIAL, curState.toString());
	  return;
	}
      }
    }
    catch (Exception e) {
        // Assert.printStack(e);
        if (curState != null)
        {
            MP.printError(EC.TLC_INITIAL_STATE, 
                    new String[] { (e.getMessage()==null)?e.toString():e.getMessage(), curState.toString() });
        } else
        {
            MP.printError(EC.GENERAL, e);  // LL changed call 7 April 2012
        }
        
        this.printSummary();
        return;
    }
    if (this.numOfGenStates == 0) {
        MP.printError(EC.TLC_NO_STATES_SATISFYING_INIT);
        return;
    }
    theInitStates.deepNormalize();

    // Start progress report thread:
    ProgressReport report = new ProgressReport();
    report.start();

    // Start simulating:
    int traceIdx = 0;
    int idx = 0;
    try {
      for (int traceCnt = 1; traceCnt <= this.traceNum; traceCnt++) {
	traceIdx = 0;
	this.aril = rng.getAril();
	curState = this.randomState(theInitStates);
	boolean inConstraints = this.tool.isInModel(curState);
	
	while (traceIdx < this.traceDepth) {
	  if (traceIdx < this.stateTrace.length) {
	    this.stateTrace[traceIdx] = curState;
	    traceIdx++;
	  }

	  if (!inConstraints) break;

	  StateVec nextStates = this.randomNextStates(curState);
	  if (nextStates == null) {
	    if (this.checkDeadlock) {
	      // We get here because of deadlock:
	      this.printBehavior(EC.TLC_DEADLOCK_REACHED, null, curState, traceIdx);
	      if (!TLCGlobals.continuation) { return; }
	    }
	    break;	    
	  }
	  for (int i = 0; i < nextStates.size(); i++) {
	    this.numOfGenStates++;
	    TLCState state = nextStates.elementAt(i);

	    if (TLCGlobals.coverageInterval >= 0) {
	      ((TLCStateMutSource)state).addCounts(this.astCounts);
	    }

	    if (!this.tool.isGoodState(state)) {
	      this.printBehavior(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT, null, state, traceIdx);
	      return;
	    }
	    else {
	      try {
		for (idx = 0; idx < this.invariants.length; idx++) {
		  if (!this.tool.isValid(this.invariants[idx], state)) {
		    // We get here because of invariant violation:
		    this.printBehavior(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, new String[]{this.tool.getInvNames()[idx]}, state, traceIdx);
		    if (!TLCGlobals.continuation) { return; }
		  }
		}
	      }
	      catch (Exception e) {
		// Assert.printStack(e);
	          this.printBehavior(EC.TLC_INVARIANT_EVALUATION_FAILED, new String[]{this.tool.getInvNames()[idx], e.getMessage()}, state, traceIdx);
		return;
	      }

	      try {
		for (idx = 0; idx < this.impliedActions.length; idx++) {
		  if (!this.tool.isValid(this.impliedActions[idx], curState, state)) {
		    // We get here because of implied-action violation:
		    
		    this.printBehavior(EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR, new String[]{this.tool.getImpliedActNames()[idx]}, state, traceIdx);
		    if (!TLCGlobals.continuation) { return; }
		  }
		}
	      }
	      catch (Exception e) {
		// Assert.printStack(e);
		this.printBehavior(EC.TLC_ACTION_PROPERTY_EVALUATION_FAILED, new String[]{this.tool.getImpliedActNames()[idx], e.getMessage()}, state, traceIdx);
		return;
	      }
	    }
	  }
	  TLCState s1 = this.randomState(nextStates);
	  inConstraints = (this.tool.isInModel(s1) &&
			   this.tool.isInActions(curState, s1));
	  curState = s1;
	}

	// Check if the current trace satisfies liveness properties.
        if (this.checkLiveness) {
          LiveCheck1.checkTrace(stateTrace, traceIdx);
        }

    	// Write the trace out if desired.  The trace is printed in the
    	// format of TLA module, so that it can be read by TLC again. 
    	if (this.traceFile != null) 
    	{
    	    String fileName = this.traceFile + traceCnt;
    	    // TODO is it ok here?
    	    PrintWriter pw = new PrintWriter(FileUtil.newBFOS(fileName));
    	    pw.println("---------------- MODULE " + fileName + " -----------------");
    	    for (idx = 0; idx < traceIdx; idx++) {
    	        pw.println("STATE_" + (idx+1) + " == ");
    	        pw.println(this.stateTrace[idx] + "\n");
    	    }
    	    pw.println("=================================================");	  
    	    pw.close();
    	}
      }
    }
    catch (Throwable e) {
      // Assert.printStack(e);
      if (e instanceof LiveException) 
      {
          this.printSummary();
      } else {
          // LL modified error message on 7 April 2012
          this.printBehavior(EC.GENERAL, 
                  new String[]{MP.ECGeneralMsg("", e)}, curState, traceIdx);
      }
    }
  }
  
  /**
   * Prints out the simulation behavior, in case of an error.
   * (unless we're at maximum depth, in which case don't!)
   */
  public final void printBehavior(int errorCode, String[] parameters, TLCState state, int traceIdx) 
  {
      
      MP.printError(errorCode, parameters);
      if (this.traceDepth == Long.MAX_VALUE) 
      {
          MP.printMessage(EC.TLC_ERROR_STATE);
          StatePrinter.printState(state);
      } else {
          MP.printError(EC.TLC_BEHAVIOR_UP_TO_THIS_POINT);
          TLCState lastState = null;
          for (int i = 0; i < traceIdx; i++) 
          {
              StatePrinter.printState(this.stateTrace[i], lastState, i+1);
              lastState = this.stateTrace[i];
          }
          StatePrinter.printState(state, null, traceIdx+1);
      }
      this.printSummary();
  }

  /**
   * This method returns a state that is randomly chosen from the set
   * of states.  It returns null if the set of states is empty.
   */
  public final TLCState randomState(StateVec states) throws EvalException {
    int len = states.size();
    if (len > 0) {
      int index = (int)Math.floor(this.rng.nextDouble() * len);
      return states.elementAt(index);
    }
    return null;
  }

  /* (non-Javadoc)
   * @see tlc2.tool.Cancelable#setCancelFlag(boolean)
   */
  public void setCancelFlag(boolean flag)
  {
      this.isCancelled = flag;
  }

  /**
   * This method returns the set of next states generated by a randomly
   * chosen action.  It returns null if there is no possible next state.
   */
  public final StateVec randomNextStates(TLCState state) {
    int len = this.actions.length;
    int index = (int)Math.floor(this.rng.nextDouble() * len);
    int p = this.rng.nextPrime();
    for (int i = 0; i < len; i++) {
      StateVec pstates = this.tool.getNextStates(this.actions[index], state);
      if (!pstates.empty()) {
	return pstates;
      }
      index = (index + p) % len;
    }
    return null;
  }
    
  /**
   * Prints the summary
   */
  public final void printSummary() 
  {
      this.reportCoverage();
      
      /*
       * This allows the toolbox to easily display the last set
       * of state space statistics by putting them in the same
       * form as all other progress statistics.
       */
      if (TLCGlobals.tool)
      {
          MP.printMessage(EC.TLC_PROGRESS_SIMU, String.valueOf(this.numOfGenStates));
      }
      
      MP.printMessage(EC.TLC_STATS_SIMU, new String[]{String.valueOf(this.numOfGenStates), String.valueOf(this.seed), String.valueOf(this.aril)});
  }

  /**
   * Reports coverage
   */
  public final void reportCoverage() 
  {
      if (TLCGlobals.coverageInterval >= 0) 
      {
          MP.printMessage(EC.TLC_COVERAGE_START);
          ObjLongTable counts = this.tool.getPrimedLocs();
          ObjLongTable.Enumerator keys = this.astCounts.keys();
          Object key;
          while ((key = keys.nextElement()) != null) 
          {
              String loc = ((SemanticNode)key).getLocation().toString();	
              counts.add(loc, astCounts.get(key));
          }
          Object[] skeys = counts.sortStringKeys();
          for (int i = 0; i < skeys.length; i++) {
              long val = counts.get(skeys[i]);
              MP.printMessage(EC.TLC_COVERAGE_VALUE, new String[]{skeys[i].toString(), String.valueOf(val)});
          }
          MP.printMessage(EC.TLC_COVERAGE_END);
      }
  }

  /**
   * Reports progress information
   */
  final class ProgressReport extends Thread 
  {
      public void run() 
      {
          int count = TLCGlobals.coverageInterval/TLCGlobals.progressInterval;
          try {
              while (true) 
              {
                  synchronized(this) 
                  {
                      this.wait(TLCGlobals.progressInterval);
                  }
                  MP.printMessage(EC.TLC_PROGRESS_SIMU, String.valueOf(numOfGenStates));
                  
                  if (count > 1) 
                  {
                      count--;
                  } else 
                  {
                      reportCoverage();
                      count = TLCGlobals.coverageInterval/TLCGlobals.progressInterval;
                  }
              }
          }
          catch (Exception e) 
          {
              // SZ Jul 10, 2009: changed from error to bug
              MP.printTLCBug(EC.TLC_REPORTER_DIED, null);
          }
      }
  }
}
