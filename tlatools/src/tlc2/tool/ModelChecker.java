// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Wed  4 Jul 2007 at 17:46:34 PST by lamport
//      modified on Fri Jan 18 11:33:51 PST 2002 by yuanyu

package tlc2.tool;

import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Future;
import java.util.stream.Collectors;

import tla2sany.semantic.ExprNode;
import tla2sany.semantic.OpDeclNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.FPSetFactory;
import tlc2.tool.liveness.LiveCheck;
import tlc2.tool.queue.DiskByteArrayQueue;
import tlc2.tool.queue.DiskStateQueue;
import tlc2.tool.queue.IStateQueue;
import tlc2.util.IStateWriter;
import tlc2.util.SetOfStates;
import tlc2.util.statistics.BucketStatistics;
import util.Assert;
import util.DebugPrinter;
import util.FileUtil;
import util.FilenameToStream;
import util.UniqueString;

/** 
 *  A TLA+ Model checker
 */
// SZ Feb 20, 2009: major refactoring of this class introduced due to the changes
// in the type hierarchy. multiple methods has been pulled up to the super class.
// unused constructors has been removed
// the class now contains only the parts, which are different from the DFIDModelChecker
// the name resolver and support for the external specification object has been added
public class ModelChecker extends AbstractChecker
{

	protected static final boolean coverage = TLCGlobals.isCoverageEnabled();
	/**
	 * If the state/ dir should be cleaned up after a successful model run
	 */
	public static final boolean VETO_CLEANUP = Boolean.getBoolean(ModelChecker.class.getName() + ".vetoCleanup");

	private long numberOfInitialStates;
    public FPSet theFPSet; // the set of reachable states (SZ: note the type)
    public IStateQueue theStateQueue; // the state queue
    public final ConcurrentTLCTrace trace; // the trace file
    // used to calculate the spm metric
    public long distinctStatesPerMinute, statesPerMinute = 0L;
    protected long oldNumOfGenStates, oldFPSetSize = 0L;
    /**
	 * The ratio between time spend on safety checking and liveness checking.
	 */
    private double runtimeRatio = 0d;
	/**
	 * Flag set via JMX if liveness checking should be triggered.
	 */
	private boolean forceLiveCheck = false;

    /* Constructors  */
    public ModelChecker(ITool tool, String metadir, final IStateWriter stateWriter, boolean deadlock, String fromChkpt,
            final Future<FPSet> future, long startTime) throws EvalException, IOException, InterruptedException, ExecutionException {
    	this(tool, metadir, stateWriter, deadlock, fromChkpt, startTime);
    	this.theFPSet = future.get();
    }
    
    public ModelChecker(ITool tool, String metadir, final IStateWriter stateWriter, boolean deadlock, String fromChkpt,
            final FPSetConfiguration fpSetConfig, long startTime) throws EvalException, IOException {
    	this(tool, metadir, stateWriter, deadlock, fromChkpt, startTime);
    	this.theFPSet = FPSetFactory.getFPSet(fpSetConfig).init(TLCGlobals.getNumWorkers(), metadir, tool.getRootFile());
    }
    
    /**
     * The only used constructor of the TLA+ model checker
     * SZ Feb 20, 2009
     * @param resolver name resolver to be able to load files (specs and configs) from managed environments 
     * @param specObj external SpecObj added to enable to work on existing specification 
     */
	private ModelChecker(ITool tool, String metadir, final IStateWriter stateWriter, boolean deadlock, String fromChkpt,
			long startTime) throws EvalException, IOException    {
        // call the abstract constructor
        super(tool, metadir, stateWriter, deadlock, fromChkpt, startTime);

		this.theStateQueue = useByteArrayQueue()
				? new DiskByteArrayQueue(this.metadir)
				: new DiskStateQueue(this.metadir);
        // this.theStateQueue = new MemStateQueue(this.metadir);

        // Finally, initialize the trace file:
        this.trace = new ConcurrentTLCTrace(this.metadir, this.tool.getRootFile(), this.tool);

        // Initialize all the workers:
        this.workers = new Worker[TLCGlobals.getNumWorkers()];
        for (int i = 0; i < this.workers.length; i++)
        {
            this.workers[i] = this.trace.addWorker(new Worker(i, this, this.metadir, this.tool.getRootFile()));
        }
    }

    /**
     * This method does model checking on a TLA+ spec. All the visited
     * states are stored in the variable theFPSet. All the states whose
     * next states have not been explored are stored in the variable
     * theStateQueue.
     */
    public void modelCheck() throws Exception
    {
        report("entering modelCheck()");
        
        // needed to calculate state/minute in final progress report

        boolean recovered = this.recover();
        if (!recovered)
        {

            // We start from scratch. Initialize the state queue and the
            // state set to contain all the initial states.
            if (!this.checkAssumptions())
                return;
            try
            {
                report("doInit(false)");
                MP.printMessage(EC.TLC_COMPUTING_INIT);
                // SZ Feb 23, 2009: do not ignore cancel on creation of the init states
                if (!this.doInit(false))
                {
                    report("exiting, because init failed");
                    return;
                }
            } catch (Throwable e)
            {
                report("exception in init");
                report(e);
                // Initial state computation fails with an exception:
                String msg = e.getMessage();
                /**
                 * The following code replaced code equivalent to setting msg = e.getMessage().
                 * getMessage() for a StackOverflowError returned null, producing a useless
                 * error message.  Changed by LL on 12 Mar 2010
                 */
                if (e instanceof StackOverflowError) {
                    msg = "This was a Java StackOverflowError. It was probably the result\n"
                        + "of an incorrect recursive function definition that caused TLC to enter\n"
                        + "an infinite loop when trying to compute the function or its application\n"
                        + "to an element in its putative domain." ;
                }
                if (msg == null) {
                    msg = e.toString();
                }
                if (this.errState != null)
                {
                    MP.printError(EC.TLC_INITIAL_STATE, new String[] { msg, this.errState.toString() });
                } else
                {
                    MP.printError(EC.GENERAL, msg);
                }

                // Replay the error with the error stack recorded:
                this.tool.setCallStack();
                try
                {
                    numberOfInitialStates = 0;
                    // SZ Feb 23, 2009: ignore cancel on error reporting
                    this.doInit(true);
                } catch (FingerprintException fe){
                    MP.printError(EC.TLC_FINGERPRINT_EXCEPTION, new String[]{fe.getTrace(), fe.getRootCause().getMessage()});
                } catch (Throwable e1) {
                    // Assert.printStack(e);
                    MP.printError(EC.TLC_NESTED_EXPRESSION, this.tool.getCallStack().toString());
                }
                this.printSummary(false, startTime);
                this.cleanup(false);
                report("exiting, because init failed with exception");
                return;
            }

            long statesGenerated = getStatesGenerated();
            final String plural = (statesGenerated == 1) ? "" : "s";
            if (statesGenerated == this.theFPSet.size())
            {
                MP.printMessage(EC.TLC_INIT_GENERATED1, new String[] { String.valueOf(statesGenerated), plural });
            } else
            {
                MP.printMessage(EC.TLC_INIT_GENERATED2, new String[] { String.valueOf(statesGenerated), plural,
                        String.valueOf(this.theFPSet.size()) });
            }
        }

        report("init processed");
        
        // Finished if there is no next state predicate:
        if (this.tool.getActions().length == 0)
        {
        	if (this.theStateQueue.isEmpty()) {
        		reportSuccess(this.theFPSet, getStatesGenerated());
        		this.printSummary(true, startTime);
        	} else {
        		MP.printError(EC.TLC_STATES_AND_NO_NEXT_ACTION);
        	}
            this.cleanup(true);
            report("exiting with actions.length == 0");
            return;
        }

        boolean success = false;
        try
        {
            report("running TLC");
            success = this.runTLC(Integer.MAX_VALUE);
            if (!success)
            {
                report("TLC terminated with error");
                return;
            }
            if (this.errState == null)
            {
                // Always check liveness properties at the end:
                if (this.checkLiveness)
                {
					// Print progress statistics prior to liveness checking.
					// Liveness checking can take a substantial amount of time
					// and thus give the user some clues at what stage safety
					// checking is.
            		MP.printMessage(EC.TLC_PROGRESS_STATS, new String[] {
                            String.valueOf(this.trace.getLevelForReporting()),
                            MP.format(getStatesGenerated()),
                            MP.format(theFPSet.size()),
                            MP.format(this.theStateQueue.size()) });
                	
                    report("checking liveness");
                    success = liveCheck.finalCheck(tool);
                    report("liveness check complete");
                    if (!success)
                    {
                        report("exiting error status on liveness check");
                        return;
                    }
                }

                // We get here because the checking has been completed.
                success = true;
                reportSuccess(this.theFPSet, getStatesGenerated());
            } else if (this.keepCallStack)
            {
                // Replay the error with the error stack recorded:
                this.tool.setCallStack();
                try
                {
					// Not adding newly created Worker to trace#addWorker because it is not supposed
					// to rewrite the trace file but to reconstruct actual states referenced by
					// their fingerprints in the trace.
					this.doNext(this.predErrState, this.checkLiveness ? new SetOfStates() : null,
							new Worker(4223, this, this.metadir, tool.getRootFile()));
                } catch (FingerprintException e)
                {
                    MP.printError(EC.TLC_FINGERPRINT_EXCEPTION, new String[]{e.getTrace(), e.getRootCause().getMessage()});
                } catch (Throwable e)
                {
                    // Assert.printStack(e);
                    MP.printError(EC.TLC_NESTED_EXPRESSION, this.tool.getCallStack().toString());
                }
            }
        } catch (Exception e)
        {
            report("TLC terminated with error");
            // Assert.printStack(e);
            success = false;
            MP.printError(EC.GENERAL, e);  // LL changed call 7 April 2012
        } finally
        {
        	
        	this.printSummary(success, startTime);

        	if (this.checkLiveness) {
				if (LIVENESS_STATS) {
					// Reclaim memory for in-degree calculation
					System.gc();

					MP.printStats(liveCheck
							.calculateInDegreeDiskGraphs(new BucketStatistics("Histogram vertex in-degree",
									LiveCheck.class.getPackage().getName(), "DiskGraphsInDegree")),
							liveCheck.getOutDegreeStatistics());
				}
        	}

            this.cleanup(success);
        }

        report("exiting modelCheck()");
    }

    /** 
     * Check the assumptions.  
     */
    public boolean checkAssumptions()
    {
        ExprNode[] assumps = this.tool.getAssumptions();
        boolean[] isAxiom = this.tool.getAssumptionIsAxiom();
        for (int i = 0; i < assumps.length; i++)
        {
            try
            {
                if ((!isAxiom[i]) && !this.tool.isValid(assumps[i]))
                {
                    MP.printError(EC.TLC_ASSUMPTION_FALSE, assumps[i].toString());
                    return false;
                }
            } catch (Exception e)
            {
                // Assert.printStack(e);
                MP.printError(EC.TLC_ASSUMPTION_EVALUATION_ERROR,
                        new String[] { assumps[i].toString(), e.getMessage() });
                return false;
            }
        }
        return true;
    }

    /**
     * Initialize the model checker
     * @return status, if false, the processing should be stopped
     * @throws Throwable
     */
    public final boolean doInit(boolean ignoreCancel) throws Throwable
    {
		// Generate the initial states.
        //
		// The functor is passed to getInitStates() to - instead of adding all
		// init states into an intermediate StateVec to check and add each state
		// in a subsequent loop - directly check each state one-by-one and add
		// it to the queue, fingerprint set and trace file. This avoids
		// allocating memory for StateVec (which depending on the number of init
		// states can grow to be GBs) and the subsequent loop over StateVec.
        final DoInitFunctor functor;
        if (ignoreCancel) {
			// Rerunning state space exploration to reconstruct the error stack to determine
			// what caused Tool to fail to evaluate the init predicate expressions. Thus,
			// re-check all invariants even if state is already known (= part of theFPSet).
        	functor = new DoInitFunctor(ignoreCancel);
        } else {
        	functor = new DoInitFunctor();
        }
		try {
			this.tool.getInitStates(functor);
		} catch (DoInitFunctor.InvariantViolatedException ive) {
			this.errState = functor.errState;
			return functor.returnValue;
		} catch (Assert.TLCRuntimeException e) {
			this.errState = functor.errState;
			throw e;
		}
		
		// Iff one of the init states' checks violates any properties, the
		// functor will record it.
		if (functor.errState != null) {
			this.errState = functor.errState;
			if (functor.e != null) {
				throw functor.e;
			}
		}
		
		// Return whatever the functor has recorded.
		return functor.returnValue;
	}

    /**
     * Compute the set of the next states.  For each next state, check that
     * it is a valid state, check that the invariants are satisfied, check
     * that it satisfies the constraints, and enqueue it in the state queue.
     * Return true if the model checking should stop.
     * 
     * This method is called from the workers on every step
     */
    public final boolean doNext(TLCState curState, final SetOfStates liveNextStates, final Worker worker) throws Throwable
    {
        boolean deadLocked = true;
        TLCState succState = null;
        try
        {
            for (int i = 0; i < this.tool.getActions().length; i++)
            {
				//TODO Implement IStateFunctor pattern for getNextStates() too
				// to reduce memory and runtime overhead of allocating and
				// looping StateVec. However - contrary to doInit() - doNext()
				// is incompatible to the functor when liveness checking is
				// turned on. Liveness checking does not support adding
				// nextStates one-by-one but expects to be given the whole set
				// of nextStates in a single invocation
				// (LiveCheck#addNextState(..). If this limitation is ever
				// removed, the functor pattern could be applied to doNext too.
				// Other problems are access to worker and curState. A stateless functor has no
				// access to curState and worker except when it uses thread local storage.
				final Action action = this.tool.getActions()[i];
				final StateVec nextStates = this.tool.getNextStates(action, curState);
				final int sz = nextStates.size();
				worker.incrementStatesGenerated(sz);
				deadLocked = deadLocked && (sz == 0);

                for (int j = 0; j < sz; j++)
                {
					succState = nextStates.elementAt(j);
					// Check if succState is a legal state.
                    if (!this.tool.isGoodState(succState))
                    {
                    	return doNextSetErr(curState, succState, action);
					}

					final boolean inModel = (this.tool.isInModel(succState) && this.tool.isInActions(curState, succState));
					boolean seen = false;
                    if (inModel)
                    {
						seen = isSeenState(curState, worker, succState, liveNextStates, action);
					}
					// Check if succState violates any invariant:
                    if (!seen)
                    {
                    	if (doNextCheckInvariants(curState, succState, inModel, seen)) {
                    		return true;
                    	}
					}
                    // Check if the state violates any implied action. We need to do it
                    // even if succState is not new.
                    if (doNextCheckImplied(curState, succState, inModel, seen)) {
                    	return true;
                    }
                    if (inModel && !seen) {
						// The state is inModel, unseen and neither invariants
						// nor implied actions are violated. It is thus eligible
						// for further processing by other workers.
						this.theStateQueue.sEnqueue(succState);
                    }
				}
				// Must set state to null!!!
				succState = null;
			}
			// Check for deadlock:
            if (deadLocked && this.checkDeadlock)
            {
                return doNextSetErr(curState, null, false, EC.TLC_DEADLOCK_REACHED, null);
			}
			return false;
        } catch (final Throwable e)
        {
			doNextFailed(curState, succState, e);
			throw e;
		}
    }

	private final boolean isSeenState(final TLCState curState, final Worker worker, final TLCState succState,
			final SetOfStates liveNextStates, final Action action) throws IOException {
		final long fp = succState.fingerPrint();
		final boolean seen = this.theFPSet.put(fp);
		// Write out succState when needed:
		this.allStateWriter.writeState(curState, succState, !seen, action);
		if (!seen)
		{
			// Write succState to trace only if it satisfies the
			// model constraints. Do not enqueue it yet, but wait
		    // for implied actions and invariants to be checked.
		    // Those checks - if violated - will cause model checking
		    // to terminate. Thus we cannot let concurrent workers start
		    // exploring this new state. Conversely, the state has to
		    // be in the trace in case either invariant or implied action
		    // checks want to print the trace. 
			worker.writeState(curState, fp, succState);
			if (coverage) {
				action.cm.incSecondary();
			}
		}
		// For liveness checking:
		if (this.checkLiveness)
		{
			liveNextStates.put(fp, succState);
		}
		return seen;
	}

	private final boolean doNextCheckInvariants(final TLCState curState, final TLCState succState, final boolean inModel, final boolean seen) throws IOException, WorkerException, Exception {
        int k = 0;
		try
        {
			for (k = 0; k < this.tool.getInvariants().length; k++)
            {
                if (!tool.isValid(this.tool.getInvariants()[k], succState))
                {
                    // We get here because of invariant violation:
                	if (TLCGlobals.continuation) {
                        synchronized (this)
                        {
							MP.printError(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR,
									this.tool.getInvNames()[k]);
							this.trace.printTrace(curState, succState);
							return false;
                        }
                	} else {
						return doNextSetErr(curState, succState, false,
								EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, this.tool.getInvNames()[k]);
                	}
				}
			}
        } catch (Exception e)
        {
			doNextEvalFailed(curState, succState, EC.TLC_INVARIANT_EVALUATION_FAILED,
					this.tool.getInvNames()[k], e);
		}
		return false;
	}

	private final boolean doNextCheckImplied(final TLCState curState, final TLCState succState, final boolean inModel, boolean seen) throws IOException, WorkerException, Exception {
		int k = 0;
        try
        {
			for (k = 0; k < this.tool.getImpliedActions().length; k++)
            {
                if (!tool.isValid(this.tool.getImpliedActions()[k], curState, succState))
                {
                    // We get here because of implied-action violation:
                    if (TLCGlobals.continuation)
                    {
                        synchronized (this)
                        {
                            MP.printError(EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR, this.tool
                                    .getImpliedActNames()[k]);
							this.trace.printTrace(curState, succState);
							return false;
                       }
                    } else {
						return doNextSetErr(curState, succState, false,
								EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR,
								this.tool.getImpliedActNames()[k]);
                	}
				}
			}
        } catch (Exception e)
        {
			doNextEvalFailed(curState, succState, EC.TLC_ACTION_PROPERTY_EVALUATION_FAILED,
					this.tool.getImpliedActNames()[k], e);
		}
        return false;
	}

	private final boolean doNextSetErr(TLCState curState, TLCState succState, boolean keep, int ec, String param) throws IOException, WorkerException {
		synchronized (this)
		{
		    if (this.setErrState(curState, succState, keep))
		    {
		    	if (param == null) {
		    		MP.printError(ec);
		    	} else {
		    		MP.printError(ec, param);
		    	}
				this.trace.printTrace(curState, succState);
				this.theStateQueue.finishAll();
				this.notify();
			}
		}
		return true;
	}

	private final boolean doNextSetErr(TLCState curState, TLCState succState, Action action) throws IOException, WorkerException {
		synchronized (this) {
			if (this.setErrState(curState, succState, false))
			{
				final Set<OpDeclNode> unassigned = succState.getUnassigned();
				if (this.tool.getActions().length == 1) {
					MP.printError(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT,
							new String[] { unassigned.size() > 1 ? "s are" : " is",
									unassigned.stream().map(n -> n.getName().toString())
											.collect(Collectors.joining(", ")) });
				} else {
					MP.printError(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT,
							new String[] { action.getName().toString(),
									unassigned.size() > 1 ? "s are" : " is",
									unassigned.stream().map(n -> n.getName().toString())
											.collect(Collectors.joining(", ")) });
				}
				this.trace.printTrace(curState, succState);
				this.theStateQueue.finishAll();
				this.notify();
			}
			return true;
		}
	}

	private final void doNextEvalFailed(TLCState curState, TLCState succState, int ec, String param, Exception e)
			throws IOException, WorkerException, Exception {
		synchronized (this) {
		    if (this.setErrState(curState, succState, true))
		    {
				MP.printError(ec, new String[] { param, (e.getMessage() == null) ? e.toString() : e.getMessage() });
				this.trace.printTrace(curState, succState);
				this.theStateQueue.finishAll();
				this.notify();
			}
			throw e;
		}
	}

	private final void doNextFailed(TLCState curState, TLCState succState, Throwable e)
			throws IOException, WorkerException, Throwable {
		// Assert.printStack(e);
		final boolean keep = ((e instanceof StackOverflowError) || (e instanceof OutOfMemoryError)
		        || (e instanceof AssertionError));
		synchronized (this)
		{
		    if (this.setErrState(curState, succState, !keep))
		    {
		        if (e instanceof StackOverflowError)
		        {
					MP.printError(EC.SYSTEM_STACK_OVERFLOW, e);
		        } else if (e instanceof OutOfMemoryError)
		        {
					MP.printError(EC.SYSTEM_OUT_OF_MEMORY, e);
		        } else if (e instanceof AssertionError)
		        {
					MP.printError(EC.TLC_BUG, e);
		        } else if (e.getMessage() != null)
		        {
		            MP.printError(EC.GENERAL, e);  // LL changed call 7 April 2012
				}
				this.trace.printTrace(curState, succState);
				this.theStateQueue.finishAll();
				this.notify();
			}
		}
	}

    /**
     * Things need to be done here:
     * Check liveness: check liveness properties on the partial state graph.
     * Create checkpoint: checkpoint three data structures: the state set,
     *                    the state queue, and the state trace.
     */
    @Override
    public final boolean doPeriodicWork() throws Exception
    {
		// Remember if checkpointing should be run. doCheckPoint() when called
		// internally diffs the time expired since its last invocation which is
		// only milliseconds here when called twice.
		final boolean createCheckPoint = TLCGlobals.doCheckPoint();
		if ((!this.checkLiveness || runtimeRatio > TLCGlobals.livenessRatio || !liveCheck.doLiveCheck()) && !forceLiveCheck && !createCheckPoint) {
			updateRuntimeRatio(0L);
			
			// Do not suspend the state queue if neither check-pointing nor
			// liveness-checking is going to happen. Suspending is expensive.
			// It stops all workers.
			return true;
		}
   	
        if (this.theStateQueue.suspendAll())
        {
            // Run liveness checking, if needed:
			// The ratio set in TLCGlobals defines an upper bound for the
			// runtime dedicated to liveness checking.
            if (this.checkLiveness && (runtimeRatio < TLCGlobals.livenessRatio || forceLiveCheck))
            {
        		final long preLivenessChecking = System.currentTimeMillis();
                if (!liveCheck.check(tool, forceLiveCheck)) {
                	return false;
                }
                forceLiveCheck = false;
                updateRuntimeRatio(System.currentTimeMillis() - preLivenessChecking);
            } else if (runtimeRatio > TLCGlobals.livenessRatio) {
            	updateRuntimeRatio(0L);
            }

            if (createCheckPoint) {
            	// Checkpoint:
            	MP.printMessage(EC.TLC_CHECKPOINT_START, this.metadir);
            	
            	// start checkpointing:
            	this.theStateQueue.beginChkpt();
            	this.trace.beginChkpt();
            	this.theFPSet.beginChkpt();
            	this.theStateQueue.resumeAll();
            	UniqueString.internTbl.beginChkpt(this.metadir);
            	if (this.checkLiveness)
            	{
            		liveCheck.beginChkpt();
            	}
            	// commit checkpoint:
            	this.theStateQueue.commitChkpt();
            	this.trace.commitChkpt();
            	this.theFPSet.commitChkpt();
            	UniqueString.internTbl.commitChkpt(this.metadir);
            	if (this.checkLiveness)
            	{
            		liveCheck.commitChkpt();
            	}
            	MP.printMessage(EC.TLC_CHECKPOINT_END);
            } else {
				// Just resume worker threads when checkpointing is skipped
            	this.theStateQueue.resumeAll();
            }
        }
        return true;
    }

	public void forceLiveCheck() {
		forceLiveCheck = true;
	}
    
    protected void updateRuntimeRatio(final long delta) {
    	assert delta >= 0L;

    	// Absolute runtime from TLC startup to now (includes liveness
		// checking, even the current delta).
		long totalRuntime = System.currentTimeMillis() - startTime;
		
		// Subtract a progressInterval to account for the fact that the
		// previously recorded runtimeRatio was calculated with totalRuntime
		// from the previous progressReporting interval. updateRuntimeRatio is
		// called from doPeriodicWork which executes every progressIntervall.
		// This is an approximation because the last invocation could have
		// happened longer ago than progressInterval if e.g. checkpointing
		// blocked the doPeriodicWork thread.
		totalRuntime = totalRuntime - TLCGlobals.progressInterval;
		
		// Subtract delta from the totalRuntime
		totalRuntime = totalRuntime - delta;
		
		// Absolute time spent on all liveness checks from TLC
		// startup up to now (without delta). Iff no liveness checking has been
		// executed so far, the absolute time is obviously 0. totalRuntime
		// can also be negative.
		final double absLivenessRuntime = Math.max(totalRuntime * runtimeRatio, 0);

		// Sum up the absLivenessRuntime with the new delta. It is the current
		// absolute time for liveness checking. Divide it by overall
		// totalRuntime (including progressInterval and delta) to calculate the
		// new ratio.
		runtimeRatio = (delta + absLivenessRuntime) / (totalRuntime + TLCGlobals.progressInterval + delta);
    }
    
    public double getRuntimeRatio() {
    	return runtimeRatio;
    }

    public final boolean recover() throws IOException
    {
        boolean recovered = false;
        if (this.fromChkpt != null)
        {
            // We recover from previous checkpoint.
            MP.printMessage(EC.TLC_CHECKPOINT_RECOVER_START, this.fromChkpt);
            this.trace.recover();
            this.theStateQueue.recover();
            this.theFPSet.recover(this.trace);
            if (this.checkLiveness)
            {
				// Liveness checking requires the initial states to be
				// available as part of behaviors. Initial states are not part
				// of the checkpoint, but we can easily recreate them.
				// See bug #22 "Recovering from a checkpoint silently breaks
				// liveness checking" at
				// https://github.com/tlaplus/tlaplus/issues/22
            	this.tool.getInitStates(new IStateFunctor() {
					public Object addElement(TLCState state) {
						liveCheck.addInitState(tool, state, state.fingerPrint());
						return true;
					}
				});
                liveCheck.recover();
            }
            MP.printMessage(EC.TLC_CHECKPOINT_RECOVER_END, new String[] { String.valueOf(this.theFPSet.size()),
                    String.valueOf(this.theStateQueue.size()) });
            recovered = true;
            // Not all states are true initial states, but who cares at this point?
            numberOfInitialStates = this.theFPSet.size();
        }
        return recovered;
    }

    private final void cleanup(boolean success) throws IOException
    {
        this.theFPSet.close();
        this.trace.close();
        if (this.checkLiveness) {
        	liveCheck.close();
        }
        this.allStateWriter.close();
    	if (!VETO_CLEANUP) {
    		FileUtil.deleteDir(this.metadir, success);
    	}
	}

    public final void printSummary(boolean success, final long startTime) throws IOException
    {
        super.reportCoverage(this.workers);
        
        /*
         * This allows the toolbox to easily display the last set
         * of state space statistics by putting them in the same
         * form as all other progress statistics.
         */
        if (TLCGlobals.tool)
        {	
        	printProgresStats(startTime);
        }

        MP.printMessage(EC.TLC_STATS, new String[] { String.valueOf(getStatesGenerated()),
                String.valueOf(this.theFPSet.size()), String.valueOf(this.theStateQueue.size()) });
        if (success)
        {
            MP.printMessage(EC.TLC_SEARCH_DEPTH, String.valueOf(this.trace.getLevelForReporting()));
			
        	// Aggregate outdegree from statistics maintained by individual workers. 
        	final BucketStatistics aggOutDegree = new BucketStatistics("State Graph OutDegree");
        	for (IWorker worker : workers) {
				aggOutDegree.add(((Worker) worker).getOutDegree());
			}
        	// Print graph statistics iff data points were actually collected.
        	if (aggOutDegree.getObservations() > 0) {
				MP.printMessage(EC.TLC_STATE_GRAPH_OUTDEGREE,
						new String[] { Integer.toString(aggOutDegree.getMin()),
								Long.toString(Math.round(aggOutDegree.getMean())),
								Long.toString(Math.round(aggOutDegree.getPercentile(.95))),
								Integer.toString(aggOutDegree.getMax()) });
        	}
        }
    }
    
    private final void printProgresStats(final long startTime) throws IOException {
        final long fpSetSize = this.theFPSet.size();
        
        // print progress showing states per minute metric (spm)
        final double factor;
        if (startTime < 0) {
        	factor = TLCGlobals.progressInterval / 60000d;
        } else {
        	// This is final statistics
        	oldNumOfGenStates = 0;
        	oldFPSetSize = 0;
        	factor = (System.currentTimeMillis() - startTime) / 60000d;
        }
		final long l = getStatesGenerated();
		statesPerMinute = (long) ((l - oldNumOfGenStates) / factor);
        oldNumOfGenStates = l;
        distinctStatesPerMinute = (long) ((fpSetSize - oldFPSetSize) / factor);
        oldFPSetSize = fpSetSize;
        
		MP.printMessage(EC.TLC_PROGRESS_STATS, new String[] {
                String.valueOf(this.trace.getLevelForReporting()),
                MP.format(l),
                MP.format(fpSetSize),
                MP.format(this.theStateQueue.size()),
                MP.format(statesPerMinute),
                MP.format(distinctStatesPerMinute) });
    }

    public static final void reportSuccess(final FPSet anFpSet, final long numOfGenStates) throws IOException
    {
        final long numOfDistinctStates = anFpSet.size();
        final double optimisticProb = calculateOptimisticProbability(numOfDistinctStates, numOfGenStates);
        if (optimisticProb < 1E-10) {
			// If the optimistic probability is sufficiently low, don't waste time
			// calculating the actual probability.
        	reportSuccess(numOfDistinctStates, numOfGenStates);
        } else {
        	reportSuccess(numOfDistinctStates, anFpSet.checkFPs(), numOfGenStates);
        }
    }

    /**
     * Spawn the worker threads
     */
    protected IWorker[] startWorkers(AbstractChecker checker, int checkIndex)
    {
		// Generation of initial states is done at this point. Thus set the
		// number of workers on the fpset, for it to adapt any synchronization
    	// if necessary (e.g. OffHeapDiskFPSet).
        this.theFPSet.incWorkers(this.workers.length);

        for (int i = 0; i < this.workers.length; i++)
        {
            this.workers[i].start();
        }
        return this.workers;
    }

    /**
     * Process calculation.  
     * 
     * Comments added 9 April 2012 by LL.  The above was Simon's extensive commenting.  I presume
     * he really mean "ProGRess calculation", since this seems to be where the coverage
     * and progress information is written.  The method writes the progress information,
     * prints the coverage only if count = 0, and then waits until it's time to print
     * the next progress report before exiting.  (The next progress report is printed
     * the next time the method is called.)  
     * 
     * It looks like this is where the depth-first model checker exits when it has
     * finished checking the required depth, but I'm not sure.
     * 
     * @param count
     * @param depth
     * @throws Exception
     */
    protected void runTLCContinueDoing(final int count, final int depth) throws Exception
    {
        final int level = this.trace.getLevel();
        
    	printProgresStats(-1);
        
        if (level > depth)
        {
            this.theStateQueue.finishAll();
            this.done = true;
        } else
        {
            // The following modification sof count are obviously bogus and
            // resulted from Simon's modification of Yuan's original code.
            // Yuan's original code assumes coverageInterval >= progressInterval,
            // and this should eventually be changed. But for now,
            // the caller of this method is responsible for updating
            // count. LL 9 Oct 2009
            if (count == 0)
            {
                super.reportCoverage(this.workers);
                // count = TLCGlobals.coverageInterval / TLCGlobals.progressInterval;
            } // else
            // {
            // count--;
            // }
            this.wait(TLCGlobals.progressInterval);
        }
    }

    /**
     * Debugging support
     * @param e
     */
    private void report(Throwable e)
    {
        DebugPrinter.print(e);
    }
    
	private static boolean useByteArrayQueue() {
		return Boolean.getBoolean(ModelChecker.class.getName() + ".BAQueue");
	}

	public static String getStateQueueName() {
		// Ideally, this wouldn't hard-code the simple name of the classes but we don't
		// have access to the class file yet.
		return useByteArrayQueue() ? "DiskByteArrayQueue" : "DiskStateQueue";
	}

    public long getStatesGenerated() {
    	long sum = numberOfInitialStates;
    	for (final IWorker worker : workers) {
			sum += ((Worker) worker).getStatesGenerated();
		}
    	return sum;
    }

	/* (non-Javadoc)
	 * @see tlc2.tool.AbstractChecker#getProgress()
	 */
	@Override
	public int getProgress() {
		try {
			return trace.getLevelForReporting();
		} catch (IOException e) {
			// The modelchecker trace file might be closed already (e.g. it
			// gets closed at the end of the modelchecker run)
			return -1;
		}
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.AbstractChecker#stop()
	 */
	@Override
	public void stop() {
		synchronized (this) {
			this.setDone();
			this.theStateQueue.finishAll();
			this.notifyAll();
		}
	}
	
	public void suspend() {
		synchronized (this) {
			this.theStateQueue.suspendAll();
			this.notifyAll();
		}
	}

	public void resume() {
		synchronized (this) {
			this.theStateQueue.resumeAll();
			this.notifyAll();
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.AbstractChecker#getStateQueueSize()
	 */
	@Override
	public long getStateQueueSize() {
		return theStateQueue.size();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.AbstractChecker#getDistinctStatesGenerated()
	 */
	@Override
	public long getDistinctStatesGenerated() {
		return theFPSet.size();
	}
   
	/**
	 * An implementation of {@link IStateFunctor} for
	 * {@link ModelChecker#doInit(boolean)}.
	 */
	private class DoInitFunctor implements IStateFunctor {

		@SuppressWarnings("serial")
		public class InvariantViolatedException extends RuntimeException {
		}
		
		/**
		 * Non-Null iff a violation occurred.
		 */
		private TLCState errState;
		private Throwable e;

		/**
		 * The return values of addElement are meaningless, but doInit wants to
		 * know the actual outcome when all init states have been processed.
		 * This outcome is stored as returnValue.
		 */
		private boolean returnValue = true;
		
		private final boolean forceChecks;
		
		public DoInitFunctor() {
			this(false);
		}
		
		public DoInitFunctor(boolean forceChecks) {
			this.forceChecks = forceChecks;
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.IStateFunctor#addElement(tlc2.tool.TLCState)
		 */
		public Object addElement(final TLCState curState) {
			if (Long.bitCount(numberOfInitialStates) == 1 && numberOfInitialStates > 1) {
				MP.printMessage(EC.TLC_COMPUTING_INIT_PROGRESS, Long.toString(numberOfInitialStates));
			}
			numberOfInitialStates++;
			
			// getInitStates() does not support aborting init state generation
			// once a violation has been found (that is why the return values of
			// addElement are meaningless). It continues until all init
			// states have been generated. Thus, the functor simply ignores
			// subsequent states once a violation has been recorded.
			if (errState != null) {
				returnValue = false;
				return returnValue;
			}
			
			try {
				// Check if the state is a legal state
				if (!tool.isGoodState(curState)) {
					MP.printError(EC.TLC_INITIAL_STATE, new String[]{ "current state is not a legal state", curState.toString() });
					this.errState = curState;
					returnValue = false;
					throw new InvariantViolatedException();
				}
				boolean inModel = tool.isInModel(curState);
				boolean seen = false;
				if (inModel) {
					long fp = curState.fingerPrint();
					seen = theFPSet.put(fp);
					if (!seen) {
						allStateWriter.writeState(curState);
						((Worker) workers[0]).writeState(curState, fp);
						theStateQueue.enqueue(curState);

						// build behavior graph for liveness checking
						if (checkLiveness) {
							liveCheck.addInitState(tool, curState, fp);
						}
					}
				}
				// Check properties of the state:
				if (!seen || forceChecks) {
					for (int j = 0; j < tool.getInvariants().length; j++) {
						if (!tool.isValid(tool.getInvariants()[j], curState)) {
							// We get here because of invariant violation:
							MP.printError(EC.TLC_INVARIANT_VIOLATED_INITIAL,
									new String[] { tool.getInvNames()[j].toString(), curState.toString() });
							if (!TLCGlobals.continuation) {
								this.errState = curState;
								returnValue = false;
								throw new InvariantViolatedException();
							}
						}
					}
					for (int j = 0; j < tool.getImpliedInits().length; j++) {
						if (!tool.isValid(tool.getImpliedInits()[j], curState)) {
							// We get here because of implied-inits violation:
							MP.printError(EC.TLC_PROPERTY_VIOLATED_INITIAL,
									new String[] { tool.getImpliedInitNames()[j], curState.toString() });
							this.errState = curState;
							returnValue = false;
							throw new InvariantViolatedException();
						}
					}
				}
			} catch (InvariantViolatedException | Assert.TLCRuntimeException e) {
				// IVE gets thrown above when an Invariant is violated. TLCRuntimeException gets
				// thrown when Tool fails to evaluate a statement because of e.g. too large sets
				// or type errors such as in DoInitFunctorInvariantMinimalErrorStackTest test.
				this.errState = curState;
				this.e = e;
				throw e;
			} catch (OutOfMemoryError e) {
				MP.printError(EC.SYSTEM_OUT_OF_MEMORY_TOO_MANY_INIT);
				returnValue = false;
				return returnValue;
			} catch (Throwable e) {
				// Assert.printStack(e);
				this.errState = curState;
				this.e = e;
			}
			return returnValue;
		}
	}

	public List<File> getModuleFiles(FilenameToStream resolver) {
		return this.tool.getModuleFiles(resolver);
	}
}
	