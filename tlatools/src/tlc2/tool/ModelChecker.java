// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed  4 Jul 2007 at 17:46:34 PST by lamport  
//      modified on Fri Jan 18 11:33:51 PST 2002 by yuanyu   

package tlc2.tool;

import java.io.IOException;
import java.util.concurrent.atomic.AtomicLong;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ExprNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.FPSetFactory;
import tlc2.tool.liveness.LiveCheck;
import tlc2.tool.queue.DiskStateQueue;
import tlc2.tool.queue.IStateQueue;
import tlc2.util.IdThread;
import tlc2.util.LongVec;
import tlc2.util.ObjLongTable;
import tlc2.util.statistics.BucketStatistics;
import tlc2.value.Value;
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

	/**
	 * If the state/ dir should be cleaned up after a successful model run
	 */
	private static final boolean VETO_CLEANUP = Boolean.getBoolean(ModelChecker.class.getName() + ".vetoCleanup");

    public FPSet theFPSet; // the set of reachable states (SZ: note the type)
    public IStateQueue theStateQueue; // the state queue
    public TLCTrace trace; // the trace file
    protected Worker[] workers; // the workers
    // used to calculate the spm metric
    public long distinctStatesPerMinute, statesPerMinute = 0L;
    protected long oldNumOfGenStates, oldFPSetSize = 0L;
    /**
     * Timestamp of when model checking started.
     */
    private final long startTime = System.currentTimeMillis();
    /**
	 * The ratio between time spend on safety checking and liveness checking.
	 */
    private double runtimeRatio = 0d;
	/**
	 * Flag set via JMX if liveness checking should be triggered.
	 */
	private boolean forceLiveCheck = false;

    /* Constructors  */
    /**
     * The only used constructor of the TLA+ model checker
     * SZ Feb 20, 2009
     * @param resolver name resolver to be able to load files (specs and configs) from managed environments 
     * @param specObj external SpecObj added to enable to work on existing specification 
     * Modified on 6 Apr 2010 by Yuan Yu to add fpMemSize parameter.
     */
    public ModelChecker(String specFile, String configFile, String dumpFile, boolean deadlock, String fromChkpt,
            FilenameToStream resolver, SpecObj specObj, final FPSetConfiguration fpSetConfig) throws EvalException, IOException
    {
        // call the abstract constructor
        super(specFile, configFile, dumpFile, deadlock, fromChkpt, true, resolver, specObj);

        // SZ Feb 20, 2009: this is a selected alternative
        this.theStateQueue = new DiskStateQueue(this.metadir);
        // this.theStateQueue = new MemStateQueue(this.metadir);

        //TODO why used to div by 20?
		this.theFPSet = FPSetFactory.getFPSet(fpSetConfig);

        // initialize the set
        this.theFPSet.init(TLCGlobals.getNumWorkers(), this.metadir, specFile);

        // Finally, initialize the trace file:
        this.trace = new TLCTrace(this.metadir, specFile, this.tool);

        // Initialize all the workers:
        this.workers = new Worker[TLCGlobals.getNumWorkers()];
        for (int i = 0; i < this.workers.length; i++)
        {
            this.workers[i] = new Worker(i, this);
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
                    this.numOfGenStates = new AtomicLong(0);
                    // SZ Feb 23, 2009: ignore cancel on error reporting
                    this.doInit(true);
                } catch (Throwable e1)
                {
                    // Assert.printStack(e);
                    MP.printError(EC.TLC_NESTED_EXPRESSION, this.tool.getCallStack().toString());
                }
                this.printSummary(false, startTime);
                this.cleanup(false);
                report("exiting, because init failed with exception");
                return;
            }

            if (this.numOfGenStates.get() == this.theFPSet.size())
            {
                String plural = (this.numOfGenStates.get() == 1) ? "" : "s";
                MP.printMessage(EC.TLC_INIT_GENERATED1, new String[] { String.valueOf(this.numOfGenStates), plural });
            } else
            {
                MP.printMessage(EC.TLC_INIT_GENERATED1, new String[] { String.valueOf(this.numOfGenStates),
                        String.valueOf(this.theFPSet.size()) });
            }
        }

        report("init processed");
        // Finished if there is no next state predicate:
        if (this.actions.length == 0)
        {
            reportSuccess(this.theFPSet, this.numOfGenStates.get());
            this.printSummary(true, startTime);
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
                    report("checking liveness");
                    success = liveCheck.finalCheck();
                    report("liveness check complete");
                    if (!success)
                    {
                        report("exiting error status on liveness check");
                        return;
                    }
                }

                // We get here because the checking has been completed.
                success = true;
                reportSuccess(this.theFPSet, this.numOfGenStates.get());
            } else if (this.keepCallStack)
            {
                // Replay the error with the error stack recorded:
                this.tool.setCallStack();
                try
                {
                    this.doNext(this.predErrState, new ObjLongTable(10));
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
		// SZ Feb 23, 2009: cancel flag set, quit
        if (!ignoreCancel && this.cancellationFlag)
        {
			return false;
		}

		// Generate the initial states.
        //
		// The functor is passed to getInitStates() to - instead of adding all
		// init states into an intermediate StateVec to check and add each state
		// in a subsequent loop - directly check each state one-by-one and add
		// it to the queue, fingerprint set and trace file. This avoids
		// allocating memory for StateVec (which depending on the number of init
		// states can grow to be GBs) and the subsequent loop over StateVec.
		final DoInitFunctor functor = new DoInitFunctor();
		this.tool.getInitStates(functor);
		
		// Iff one of the init states' checks violates any properties, the
		// functor will record it.
		if (functor.errState != null) {
			this.errState = functor.errState;
			throw functor.e;
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
    public final boolean doNext(TLCState curState, ObjLongTable counts) throws Throwable
    {
        // SZ Feb 23, 2009: cancel the calculation
        if (this.cancellationFlag)
        {
            return false;
        }

        boolean deadLocked = true;
        TLCState succState = null;
        StateVec liveNextStates = null;
        LongVec liveNextFPs = null;

        if (this.checkLiveness)
        {
            liveNextStates = new StateVec(2);
            liveNextFPs = new LongVec(2);
        }

        try
        {
			int k = 0;
			// <--
			// <--
            for (int i = 0; i < this.actions.length; i++)
            {
				// SZ Feb 23, 2009: cancel the calculation
                if (this.cancellationFlag)
                {
					return false;
				}

				//TODO Implement IStateFunctor pattern for getNextStates() too
				// to reduce memory and runtime overhead of allocating and
				// looping StateVec. However - contrary to doInit() - doNext()
				// is incompatible to the functor when liveness checking is
				// turned on. Liveness checking does not support adding
				// nextStates one-by-one but expects to be given the whole set
				// of nextStates in a single invocation
				// (LiveCheck#addNextState(..). If this limitation is ever
				// removed, the functor pattern could be applied to doNext too.
				StateVec nextStates = this.tool.getNextStates(this.actions[i], curState);
				int sz = nextStates.size();
				this.incNumOfGenStates(sz);
				deadLocked = deadLocked && (sz == 0);

                SUCCESSORS: for (int j = 0; j < sz; j++)
                {
					succState = nextStates.elementAt(j);
					// Check if succState is a legal state.
                    if (!this.tool.isGoodState(succState))
                    {
                        if (this.setErrState(curState, succState, false))
                        {
							MP.printError(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT);
							this.trace.printTrace(curState, succState);
							this.theStateQueue.finishAll();

                            synchronized (this)
                            {
								this.notify();
							}
						}
						return true;
					}
                    if (TLCGlobals.coverageInterval >= 0)
                    {
						((TLCStateMutSource) succState).addCounts(counts);
					}

					final boolean inModel = (this.tool.isInModel(succState) && this.tool.isInActions(curState, succState));
					boolean seen = false;
                    if (inModel)
                    {
						long fp = succState.fingerPrint();
						seen = this.theFPSet.put(fp);
                        if (!seen)
                        {
							// Write out succState when needed:
                            if (this.allStateWriter != null)
                            {
								this.allStateWriter.writeState(succState);
							}
							// Write succState to trace only if it satisfies the
							// model constraints. Do not enqueue it yet, but wait
                            // for implied actions and invariants to be checked.
                            // Those checks - if violated - will cause model checking
                            // to terminate. Thus we cannot let concurrent workers start
                            // exploring this new state. Conversely, the state has to
                            // be in the trace in case either invariant or implied action
                            // checks want to print the trace. 
							long loc = this.trace.writeState(curState, fp);
							succState.uid = loc;
						}
						// For liveness checking:
                        if (this.checkLiveness)
                        {
							liveNextStates.addElement(succState);
							liveNextFPs.addElement(fp);
						}
					}
					// Check if succState violates any invariant:
                    if (!seen)
                    {
                        try
                        {
							int len = this.invariants.length;
                            INVARIANTS: for (k = 0; k < len; k++)
                            {
								// SZ Feb 23, 2009: cancel the calculation
                                if (this.cancellationFlag)
                                {
									return false;
								}

                                if (!tool.isValid(this.invariants[k], succState))
                                {
                                    // We get here because of invariant violation:
                                    synchronized (this)
                                    {
                                        if (TLCGlobals.continuation)
                                        {
											MP.printError(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR,
													this.tool.getInvNames()[k]);
											this.trace.printTrace(curState, succState);
											break INVARIANTS;
                                        } else
                                        {
                                            if (this.setErrState(curState, succState, false))
                                            {
                                                MP.printError(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, this.tool
                                                        .getInvNames()[k]);
												this.trace.printTrace(curState, succState);
												this.theStateQueue.finishAll();
												this.notify();
											}
											return true;
										}
									}
								}
							}
							if (k < len) {
								if (inModel && !seen) {
									// Even though the state violates an
									// invariant, add it to the queue. After
									// all, the user selected to continue model
									// checking even if an invariant is
									// violated.
									this.theStateQueue.sEnqueue(succState);
								}
								// Continue with next successor iff an
								// invariant is violated and
								// TLCGlobals.continuation is true.
								continue SUCCESSORS;
							}
                        } catch (Exception e)
                        {
                            if (this.setErrState(curState, succState, true))
                            {
                                MP.printError(EC.TLC_INVARIANT_EVALUATION_FAILED, new String[] {
                                        this.tool.getInvNames()[k], 
												(e.getMessage() == null) ? e.toString() : e.getMessage() });
								this.trace.printTrace(curState, succState);
								this.theStateQueue.finishAll();
								this.notify();
							}
							throw e;
						}
					}
                    // Check if the state violates any implied action. We need to do it
                    // even if succState is not new.
                    try
                    {
						int len = this.impliedActions.length;
                        IMPLIED: for (k = 0; k < len; k++)
                        {
							// SZ Feb 23, 2009: cancel the calculation
                            if (this.cancellationFlag)
                            {
								return false;
							}

                            if (!tool.isValid(this.impliedActions[k], curState, succState))
                            {
                                // We get here because of implied-action violation:
                                synchronized (this)
                                {
                                    if (TLCGlobals.continuation)
                                    {
                                        MP.printError(EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR, this.tool
                                                .getImpliedActNames()[k]);
										this.trace.printTrace(curState, succState);
										break IMPLIED;
                                    } else
                                    {
                                        if (this.setErrState(curState, succState, false))
                                        {
                                            MP.printError(EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR, this.tool
                                                    .getImpliedActNames()[k]);
											this.trace.printTrace(curState, succState);
											this.theStateQueue.finishAll();
											this.notify();
										}
										return true;
									}
								}
							}
						}
						if (k < len) {
							if (inModel && !seen) {
								// Even though the state violates an
								// invariant, add it to the queue. After
								// all, the user selected to continue model
								// checking even if an implied action is
								// violated.
								this.theStateQueue.sEnqueue(succState);
							}
							// Continue with next successor iff an
							// implied action is violated and
							// TLCGlobals.continuation is true.
							continue SUCCESSORS;
						}
                    } catch (Exception e)
                    {
                        if (this.setErrState(curState, succState, true))
                        {
                            MP.printError(EC.TLC_ACTION_PROPERTY_EVALUATION_FAILED, new String[] {
                                    this.tool.getImpliedActNames()[k], 
											(e.getMessage() == null) ? e.toString() : e.getMessage() });
							this.trace.printTrace(curState, succState);
							this.theStateQueue.finishAll();
							this.notify();
						}
						throw e;
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
                synchronized (this)
                {
                    if (this.setErrState(curState, null, false))
                    {
						MP.printError(EC.TLC_DEADLOCK_REACHED);
						this.trace.printTrace(curState, null);
						this.theStateQueue.finishAll();
						this.notify();
					}
				}
				return true;
			}
            // Finally, add curState into the behavior graph for liveness checking:
            if (this.checkLiveness)
            {
				// Add the stuttering step:
				long curStateFP = curState.fingerPrint();
				liveNextStates.addElement(curState);
				liveNextFPs.addElement(curStateFP);
				liveCheck.addNextState(curState, curStateFP, liveNextStates, liveNextFPs);
			}
			return false;
        } catch (Throwable e)
        {
			// Assert.printStack(e);
			boolean keep = ((e instanceof StackOverflowError) || (e instanceof OutOfMemoryError)
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
			throw e;
		}
    }

    /**
     * Things need to be done here:
     * Check liveness: check liveness properties on the partial state graph.
     * Create checkpoint: checkpoint three data structures: the state set,
     *                    the state queue, and the state trace.
     */
    public final boolean doPeriodicWork() throws Exception
    {
		if ((!this.checkLiveness || runtimeRatio > TLCGlobals.livenessRatio || !liveCheck.doLiveCheck()) && !forceLiveCheck && !TLCGlobals.doCheckPoint()) {
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
                if (!liveCheck.check(forceLiveCheck)) {
                	return false;
                }
                forceLiveCheck = false;
                updateRuntimeRatio(System.currentTimeMillis() - preLivenessChecking);
            } else if (runtimeRatio > TLCGlobals.livenessRatio) {
            	updateRuntimeRatio(0L);
            }

            if (TLCGlobals.doCheckPoint()) {
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
    
    private final void updateRuntimeRatio(long delta) {
		// Absolute runtime including liveness checking. 
		final long totalRuntime = System.currentTimeMillis() - startTime;
		// absolute time spent on liveness checking. Substract one
		// progressInterval to account for the fact that the ratio
		// was calculated with totalRuntime from the previous
		// progressReporting interval.
		final double absLivenessRuntime = Math.max(((totalRuntime - TLCGlobals.progressInterval) * runtimeRatio), 0);

		final double oldRatio = runtimeRatio;
		runtimeRatio = (delta + absLivenessRuntime) / totalRuntime;
		assert delta > 0 ? oldRatio < runtimeRatio : oldRatio > runtimeRatio;
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
            this.theFPSet.recover();
            if (this.checkLiveness)
            {
                liveCheck.recover();
            }
            MP.printMessage(EC.TLC_CHECKPOINT_RECOVER_END, new String[] { String.valueOf(this.theFPSet.size()),
                    String.valueOf(this.theStateQueue.size()) });
            recovered = true;
            this.numOfGenStates.set(this.theFPSet.size());
        }
        return recovered;
    }

    private final void cleanup(boolean success) throws IOException
    {
        this.theFPSet.close();
        this.trace.close();
        if (this.checkLiveness)
            liveCheck.close();
        if (this.allStateWriter != null)
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

        MP.printMessage(EC.TLC_STATS, new String[] { String.valueOf(this.numOfGenStates),
                String.valueOf(this.theFPSet.size()), String.valueOf(this.theStateQueue.size()) });
        if (success)
        {
            MP.printMessage(EC.TLC_SEARCH_DEPTH, String.valueOf(this.trace.getLevelForReporting()));
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
		long l = numOfGenStates.get();
		statesPerMinute = (long) ((l - oldNumOfGenStates) / factor);
        oldNumOfGenStates = l;
        distinctStatesPerMinute = (long) ((fpSetSize - oldFPSetSize) / factor);
        oldFPSetSize = fpSetSize;
        
		MP.printMessage(EC.TLC_PROGRESS_STATS, new String[] { String.valueOf(this.trace.getLevelForReporting()),
                String.valueOf(this.numOfGenStates), String.valueOf(fpSetSize),
                String.valueOf(this.theStateQueue.size()), String.valueOf(statesPerMinute), String.valueOf(distinctStatesPerMinute) });
    }

    public static final void reportSuccess(final FPSet anFpSet, final long numOfGenStates) throws IOException
    {
        final long fpSetSize = anFpSet.size();
        final double actualProb = anFpSet.checkFPs();
        reportSuccess(fpSetSize,  actualProb, numOfGenStates);
    }
    
    public static final void reportSuccess(final long numOfDistinctStates, final double actualProb, final long numOfGenStates) throws IOException
    {
        // shown as 'calculated' in Toolbox
        final double optimisticProb = numOfDistinctStates * ((numOfGenStates - numOfDistinctStates) / Math.pow(2, 64));
        /* The following code added by LL on 3 Aug 2009 to print probabilities
         * to only one decimal point.  Removed by LL on 17 April 2012 because it
         * seemed to report probabilities > 10-4 as probability 0.
         */
         // final PrintfFormat fmt = new PrintfFormat("val = %.1G");
         // final String optimisticProbStr = fmt.sprintf(optimisticProb);
         // final String actualProbStr = fmt.sprintf(actualProb);
        
        // Following two lines added by LL on 17 April 2012
        final String optimisticProbStr = "val = " + ProbabilityToString(optimisticProb, 2);
        // shown as 'observed' in Toolbox
        final String actualProbStr = "val = " + ProbabilityToString(actualProb, 2);
        MP.printMessage(EC.TLC_SUCCESS, new String[] { optimisticProbStr, actualProbStr });
    }
    
    /**
     * This method added by LL on 17 April 2012 to replace the use of the PrintfFormat
     * method in reportSuccess.
     * 
     * Returns a string representing the decimal representation of a probability to
     * a given number of significant digits.  If the input is not a probability, or if
     * some error is found, then it returns the result of applying Double.toString(long)
     * to the value.
     * 
     * Warning: the code makes the following assumption:
     *  - Double.toString(v) returns a decimal representation of v of the
     *    form  [d]* ["." [d]+ ["E" [+ | -] [d]+]  where d is a decimal digit and
     *      [x]   = 0 or 1 instance of x
     *      [x]*  = any number of instances of x
     *      [x]+  = any non-zero number of instances of x
     *      x | y = an x or a y
     * 
     * @param val                - the probability represented as a long; must satisfy 0 <= val <= 1.
     * @param significantDigits  - the number of significant digits to include; must be > 0.
     * @return
     */
    private static final String ProbabilityToString(double val, int significantDigits) {
        /*
         * If val = 0 (which shouldn't happen), return "0.0"
         */
        if (val == 0) {
            return "0.0";
        }
                
        String valString = Double.toString(val) ;
        int valStringLen = valString.length();
        
        String result = "";
        int next = 0; // pointer to the next character in valString to examine.
        int significantDigitsFound = 0;
        
        /*
         * Skip past leading zeros.
         */
        while ((next < valStringLen)  && (valString.charAt(next) == '0')) {
            next++ ;
        }
        
        /*
         * Append all the following digits to result, incrementing
         * significantDigits for each one.  
         */
        while ( (next < valStringLen)  && 
                Character.isDigit(valString.charAt(next))) {
            result = result + valString.charAt(next);
            significantDigitsFound++;
            next++ ;
         }
        
        /*
         * IF next character is not "." 
         *   THEN IF at end THEN return result
         *                  ELSE return valString.
         */
        if (next == valStringLen) {
            return result;
        } else if (valString.charAt(next) != '.') {
            return valString;
        }
        
        
        /*
         * IF significantDigitsFound >= significantDigits, 
         *    THEN skip over "." and the following digits.
         *         (this should not happen)
         *    ELSE append "." to result ;
         *         IF significantDigitsFound = 0  
         *           THEN copy each of the following "0"s of valString to result;
         *         copy up to significantDigits - significantDigitsFound
         *            following digits of valString to result;
         *         IF next char of valString a digit >= "5"
         *           THEN propagate a carry backwards over the digits of result
         *                 -- e.g., changing ".019" to ".020";
         *         Skip over remaining digits of valString;
         */
        if (significantDigitsFound >= significantDigits) {
            next++ ;
            while ( (next < valStringLen)  && 
                    Character.isDigit(valString.charAt(next))) {
                 next++ ;
             }
        } else {
            next++;
            result = result + ".";
            if (significantDigitsFound == 0) {
                while ((next < valStringLen)  && (valString.charAt(next) == '0')) {
                    next++ ;
                    result = result + "0";
                }
            }
            while ((next < valStringLen)  && 
                  Character.isDigit(valString.charAt(next)) &&
                  significantDigitsFound < significantDigits ) {
                      result = result + valString.charAt(next);
                      next++;
                      significantDigitsFound++;
             }
            if ((next < valStringLen)  &&  
                 Character.isDigit(valString.charAt(next)) &&
                 Character.digit(valString.charAt(next), 10) >= 5) {
                int prev = result.length()-1; // the next digit of result to increment
                boolean done = false;
                while (!done) {
                    if (prev < 0) {
                        result = "1" + result;
                        done = true;
                    } else {
                        char prevChar = result.charAt(prev);
                        String front = result.substring(0, prev);
                        String back = result.substring(prev+1);
                        if (Character.isDigit(prevChar)) {
                            if (prevChar == '9') {
                                result = front + '0' + back;
                            } else {
                                result = front + Character.forDigit(Character.digit(prevChar, 10)+1, 10) + back;
                                done = true;
                            }
                            
                        } else {
                            // prevChar must be '.', so just continue
                        }
                    }
                    prev--;
                }
            }
            while ((next < valStringLen)  &&  
                    Character.isDigit(valString.charAt(next))) {
                next++;
            }
        }
        
        /*
         * IF next at end of valString or at "E"
         *   THEN copy remaining chars of valString to result;
         *        return result
         *   ELSE return valString
         */
        if (next >= valStringLen) {
            return result;
        }
        if (valString.charAt(next)=='E') {
            next++;
            result = result + "E";
            while (next < valStringLen) {
                result = result + valString.charAt(next);
                next++;
            }
            return result;
        }
        return valString;
    }

// The following method used for testing ProbabilityToString
//
//    public static void main(String[] args) {
//        double[] test = new double[] {.5, .0995, .00000001, 001.000, .0022341, 
//                                      .0022351, 3.14159E-12, 
//                                      00.999, .002351111, 22.8E-14, 0.000E-12,
//                                      37, 0033D, 04.85, -35.3};
//        int i = 0;
//        while (i < test.length) {
//            System.out.println("" + i + ": " + Double.toString(test[i]) + " -> " + ProbabilityToString(test[i],2));
//            i++;
//        }    
//    }

    public final void setAllValues(int idx, Value val)
    {
        for (int i = 0; i < this.workers.length; i++)
        {
            workers[i].setLocalValue(idx, val);
        }
    }

    public final Value getValue(int i, int idx)
    {
        return workers[i].getLocalValue(idx);
    }

    /**
     * Spawn the worker threads
     */
    protected IdThread[] startWorkers(AbstractChecker checker, int checkIndex)
    {
        for (int i = 0; i < this.workers.length; i++)
        {
            this.workers[i].start();
        }
        return this.workers;
    }

    /**
     * Work to be done prior entering to the worker loop
     */
    protected void runTLCPreLoop()
    {
        // nothing to do in this implementation
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

    public long getStatesGenerated() {
    	return numOfGenStates.get();
    }
    
	/**
	 * An implementation of {@link IStateFunctor} for
	 * {@link ModelChecker#doInit(boolean)}.
	 */
	private class DoInitFunctor implements IStateFunctor {

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

		/* (non-Javadoc)
		 * @see tlc2.tool.IStateFunctor#addElement(tlc2.tool.TLCState)
		 */
		public Object addElement(final TLCState curState) {
			incNumOfGenStates(1);
			
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
					MP.printError(EC.TLC_INITIAL_STATE, curState.toString());
					return returnValue;
				}
				boolean inModel = tool.isInModel(curState);
				boolean seen = false;
				if (inModel) {
					long fp = curState.fingerPrint();
					seen = theFPSet.put(fp);
					if (!seen) {
						if (allStateWriter != null) {
							allStateWriter.writeState(curState);
						}
						curState.uid = trace.writeState(fp);
						theStateQueue.enqueue(curState);

						// build behavior graph for liveness checking
						if (checkLiveness) {
							liveCheck.addInitState(curState, fp);
						}
					}
				}
				// Check properties of the state:
				if (!seen) {
					for (int j = 0; j < invariants.length; j++) {
						if (!tool.isValid(invariants[j], curState)) {
							// We get here because of invariant violation:
							MP.printError(EC.TLC_INVARIANT_VIOLATED_INITIAL,
									new String[] { tool.getInvNames()[j].toString(), curState.toString() });
							if (!TLCGlobals.continuation) {
								returnValue = false;
								return returnValue;
							}
						}
					}
					for (int j = 0; j < impliedInits.length; j++) {
						if (!tool.isValid(impliedInits[j], curState)) {
							// We get here because of implied-inits violation:
							MP.printError(EC.TLC_PROPERTY_VIOLATED_INITIAL,
									new String[] { tool.getImpliedInitNames()[j], curState.toString() });
							returnValue = false;
							return returnValue;
						}
					}
				}
			} catch (Throwable e) {
				// Assert.printStack(e);
				if (e instanceof OutOfMemoryError) {
					MP.printError(EC.SYSTEM_OUT_OF_MEMORY_TOO_MANY_INIT);
					returnValue = false;
					return returnValue;
				}
				this.errState = curState;
				this.e = e;
			}
			return returnValue;
		}
	}
}
