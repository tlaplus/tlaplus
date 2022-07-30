// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tlc2.tool;

import java.io.IOException;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.Collectors;

import tla2sany.semantic.ExprNode;
import tla2sany.semantic.OpDeclNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.fp.dfid.FPIntSet;
import tlc2.tool.fp.dfid.MemFPIntSet;
import tlc2.tool.impl.CallStackTool;
import tlc2.tool.liveness.LiveException;
import tlc2.util.IStateWriter;
import tlc2.util.IdThread;
import tlc2.util.LongVec;
import tlc2.util.SetOfStates;
import util.Assert;
import util.FileUtil;
import util.UniqueString;

/** 
 * A TLA+ Model checker using depth-first iterative deepening 
 */
// SZ Feb 20, 2009: major refactoring of this class introduced due to the changes
// in the type hierarchy. multiple methods has been pulled up to the super class.
// unused constructors has been removed
// the class now contains only the parts, which are different from the ModelChecker
// the name resolver and support for the external specification object has been added

public class DFIDModelChecker extends AbstractChecker
{

    public TLCState[] theInitStates; // the set of initial states
    public long[] theInitFPs; // ... and their fps
    public FPIntSet theFPSet; // the set of reachable states (SZ: note the type)
    private final AtomicLong numOfGenStates;

	protected final ThreadLocal<Integer> threadLocal = new ThreadLocal<Integer>() {
		protected Integer initialValue() {
			return 1;
		}
	};

	protected static final int INITIAL_CAPACITY = 16;

    /** 
     * Constructor for running DFID   
     * @param startTime 
     * @param resolver 
     */
	public DFIDModelChecker(ITool tool, String metadir, final IStateWriter stateWriter,
			boolean deadlock, String fromChkpt, long startTime) throws EvalException, IOException {
        // call the abstract constructor
        super(tool, metadir, stateWriter, deadlock, fromChkpt, startTime);

		// https://github.com/tlaplus/tlaplus/issues/548
		Assert.check(TLCGlobals.getNumWorkers() == 1, EC.GENERAL,
				"Depth-First Iterative Deepening mode does not support multiple workers (https://github.com/tlaplus/tlaplus/issues/548).  Please run TLC with a single worker.");
		// https://github.com/tlaplus/tlaplus/issues/548
		Assert.check(this.checkLiveness == false, EC.GENERAL,
				"Depth-First Iterative Deepening mode does not support checking liveness properties (https://github.com/tlaplus/tlaplus/issues/548).  Please check liveness properties in Breadth-First-Search mode.");

		this.theInitStates = null;
        this.theInitFPs = null;
        this.theFPSet = new MemFPIntSet(); // init the state set
        this.theFPSet.init(TLCGlobals.getNumWorkers(), this.metadir, this.tool.getRootFile());

        // Initialize all the workers:
        this.workers = new DFIDWorker[TLCGlobals.getNumWorkers()];
        this.numOfGenStates = new AtomicLong(0);
    }

    /**
     * This method does model checking on a TLA+ spec. All the visited
     * states are stored in the variable theFPSet.
     */
	@Override
    protected int modelCheckImpl() throws Exception
    {
		int result = EC.NO_ERROR;
        boolean recovered = this.recover();
        try
        {
			if (this.checkLiveness && liveCheck.getNumChecker() == 0) {
				return MP.printError(EC.TLC_LIVE_FORMULA_TAUTOLOGY);
			}
			result = this.checkAssumptions();
            if (result != EC.NO_ERROR)
                return result;
            result = this.doInit(false);
            if (result != EC.NO_ERROR)
                return result;
        } catch (Throwable e)
        {
            // Initial state computation fails with an exception:
            if (this.errState != null)
            {
                MP.printError(EC.TLC_INITIAL_STATE, new String[] { e.getMessage(), this.errState.toString() });
            } else
            {
                MP.printError(EC.GENERAL, "computing initial states", e); // LL changed call 7 April 2012
            }

            // Replay the error with the error stack recorded:
            try
            {
                this.numOfGenStates.set(0);
                this.doInit(new CallStackTool(this.tool), true);
            } catch (Throwable e1)
            {
                result = MP.printError(EC.TLC_NESTED_EXPRESSION, this.tool.toString());
            }
            this.printSummary(false);
            this.cleanup(false);
            return result;
        }

        if (recovered)
        {
            MP.printMessage(EC.TLC_INIT_GENERATED3, new String[] { String.valueOf(this.numOfGenStates),
                    String.valueOf(this.theInitStates.length) });
        } else
        {
            MP.printMessage(EC.TLC_INIT_GENERATED4, new String[] { String.valueOf(this.numOfGenStates),
                    String.valueOf(this.theInitStates.length) });
        }

        // Return if there is no next state predicate:
        if (this.tool.getActions().length == 0)
        {
            this.reportSuccess();
            this.printSummary(true);
            this.cleanup(true);
            return result;
        }

        result = EC.GENERAL;
        try
        {
            boolean terminated = false;
            for (int level = 2; level <= TLCGlobals.DFIDMax; level++)
            {
                // If terminated is true, stop:
                if (terminated)
                {
                    if (this.errState == null)
                    {
                        // Always check liveness properties at the end:
                        if (this.checkLiveness)
                        {
        					// Print progress statistics prior to liveness checking.
        					// Liveness checking can take a substantial amount of time
        					// and thus give the user some clues at what stage safety
        					// checking is.
							MP.printMessage(EC.TLC_PROGRESS_STATS_DFID, new String[] {
									String.valueOf(this.numOfGenStates), String.valueOf(theFPSet.size()) });
                            // SZ Jul 10, 2009: what for?
                            // ToolIO.out.flush();
                            result = liveCheck.finalCheck(tool);
                            if (result != EC.NO_ERROR)
                                return result;
                        }

                        // We get here because the checking has been completed.
                        result = EC.NO_ERROR;
                        this.reportSuccess();
                    } else if (this.keepCallStack)
                    {
                        // Replay the error with the error stack recorded:
                    	final CallStackTool cTool = new CallStackTool(this.tool);
                        try
                        {
							this.doNext(cTool, this.predErrState, this.predErrState.fingerPrint(), true,
                                    new StateVec(1), new LongVec());
                        } catch (Throwable e)
                        {
                            MP.printError(EC.TLC_NESTED_EXPRESSION, cTool.toString());
                        }
                    }
                    break;
                }

                // Start working on this level:
                MP.printMessage(EC.TLC_PROGRESS_START_STATS_DFID, new String[] { String.valueOf(level),
                        String.valueOf(this.numOfGenStates), String.valueOf(this.theFPSet.size()) });

                FPIntSet.incLevel();
                result = this.runTLC(level);
				// Recent done flag before after the workers have checked the
				// current level in preparation for the next level.
                synchronized (this) {
                	this.done = false;
				}
                if (result != EC.NO_ERROR)
                    return result;

                // Check if we should stop at this level:
                for (int i = 0; i < this.workers.length; i++)
                {
                    if (((DFIDWorker) this.workers[i]).isTerminated())
                    {
                        terminated = true;
                        break;
                    }
                }
                boolean moreLevel = false;
                for (int i = 0; i < this.workers.length; i++)
                {
                    if (((DFIDWorker) this.workers[i]).hasMoreLevel())
                    {
                        moreLevel = true;
                        break;
                    }
                }
                terminated = terminated || !moreLevel;
            }
            return result;
        } catch (Exception e)
        {
            // Assert.printStack(e);
            if (e instanceof LiveException)
            {
                result = ((LiveException)e).errorCode;
            } else
            {
                result = MP.printError(EC.GENERAL, e);  // LL changed call 7 April 2012
            }
            return result;
        } finally
        {
        	final boolean success = result == EC.NO_ERROR;
            this.printSummary(success);
            this.cleanup(success);
        }
    }

    /* Check the assumptions.  
     * This code is a clone of the same method in ModelChecker */
    public final int checkAssumptions()
    {
        ExprNode[] assumps = this.tool.getAssumptions();
        boolean[] isAxiom = this.tool.getAssumptionIsAxiom();
        for (int i = 0; i < assumps.length; i++)
        {
            try
            {
                if ((!isAxiom[i]) && !this.tool.isValid(assumps[i]))
                {
                    return MP.printError(EC.TLC_ASSUMPTION_FALSE, assumps[i].toString());
                }
            } catch (Exception e)
            {
                // Assert.printStack(e);
                return MP.printError(EC.TLC_ASSUMPTION_EVALUATION_ERROR,
                        new String[] { assumps[i].toString(), e.getMessage() });
            }
        }
        return EC.NO_ERROR;
    }

    /* Compute the set of initial states.  */
    // SZ Feb 23, 2009: added ignore cancel flag
    public final int doInit(boolean ignoreCancel) throws Throwable {
    	return doInit(this.tool, ignoreCancel);
    }
    private final int doInit(final ITool tool, boolean ignoreCancel) throws Throwable
    {
        TLCState curState = null;
        try
        {
            // Generate the initial states:
            StateVec states = tool.getInitStates();
            this.numOfGenStates.set(states.size());
            final long l = this.numOfGenStates.get();
            //TODO casting to int is potentially dangerous
            this.theInitStates = new TLCState[(int) l];
            this.theInitFPs = new long[(int) l];
            int idx = 0;
            for (int i = 0; i < l; i++)
            {
                curState = states.elementAt(i);
                // Check if the state is a legal state
                if (!tool.isGoodState(curState))
                {
                    return MP.printError(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_INITIAL, curState.toString());
                }
                boolean inModel = tool.isInModel(curState);
                int status = FPIntSet.NEW;
                if (inModel)
                {
                    long fp = curState.fingerPrint();
                    status = this.theFPSet.setStatus(fp, FPIntSet.NEW);
                    if (status == FPIntSet.NEW)
                    {
                        this.theInitStates[idx] = curState;
                        this.theInitFPs[idx++] = fp;

                        // Write out the state if asked
                        this.allStateWriter.writeState(curState);

                        // build behavior graph for liveness checking
                        if (this.checkLiveness)
                        {
                            liveCheck.addInitState(tool, curState, fp);
                        }
                    }
                }
                // Check properties of the state:
                if (status == FPIntSet.NEW)
                {
                    for (int j = 0; j < tool.getInvariants().length; j++)
                    {
                        if (!tool.isValid(tool.getInvariants()[j], curState))
                        {
                            // We get here because of invariant violation:
                            MP.printError(EC.TLC_INVARIANT_VIOLATED_INITIAL, new String[] { tool.getInvNames()[j],
                            		tool.evalAlias(curState, curState).toString() });
                            if (!TLCGlobals.continuation)
                                return EC.TLC_INVARIANT_VIOLATED_INITIAL;
                        }
                    }
                    for (int j = 0; j < tool.getImpliedInits().length; j++)
                    {
                        if (!tool.isValid(tool.getImpliedInits()[j], curState))
                        {
                            // We get here because of implied-inits violation:
                            return MP.printError(EC.TLC_PROPERTY_VIOLATED_INITIAL, new String[] {
                                    tool.getImpliedInitNames()[j], tool.evalAlias(curState, curState).toString() });
                        }
                    }
                }
            }

            // Set up the initial pairs correctly:
            if (idx < this.numOfGenStates.get())
            {
                TLCState[] stateTemp = new TLCState[idx];
                long[] fpTemp = new long[idx];
                System.arraycopy(this.theInitStates, 0, stateTemp, 0, idx);
                System.arraycopy(this.theInitFPs, 0, fpTemp, 0, idx);
                this.theInitStates = stateTemp;
                this.theInitFPs = fpTemp;
            }
        } catch (Throwable e)
        {
            // Assert.printStack(e);
            if (e instanceof OutOfMemoryError)
            {
                return MP.printError(EC.SYSTEM_OUT_OF_MEMORY_TOO_MANY_INIT);
            }
            this.errState = curState;
            throw e;
        }
        return EC.NO_ERROR;
    }

    /**
     * Compute the set of the next states.  For each next state, check
     * if it is a valid state, if the invariants are satisfied, and if
     * it satisfies the constraints. It also adds the states that have
     * not been done in nextStates.  Return true if it finds a leaf
     * successor of curState.
     */
    public final boolean doNext(TLCState curState, long cfp, boolean isLeaf, StateVec states,
            LongVec fps) throws Throwable {
    	return doNext(this.tool, curState, cfp, isLeaf, states, fps);
    }
    public final boolean doNext(final ITool tool, TLCState curState, long cfp, boolean isLeaf, StateVec states,
            LongVec fps) throws Throwable
    {
        boolean deadLocked = true;
        TLCState succState = null;
        SetOfStates liveNextStates = null;

        if (this.checkLiveness && isLeaf)
        {
            liveNextStates = new SetOfStates(INITIAL_CAPACITY * threadLocal.get());
        }

        try
        {
            int k = 0;
            boolean allSuccDone = true;
            boolean allSuccNonLeaf = true;
            for (int i = 0; i < tool.getActions().length; i++)
            {
                StateVec nextStates = tool.getNextStates(tool.getActions()[i], curState);
                int sz = nextStates.size();
                this.numOfGenStates.getAndAdd(sz);
                deadLocked = deadLocked && (sz == 0);

                for (int j = 0; j < sz; j++)
                {
                    succState = nextStates.elementAt(j);
                    // Check if the state is a legal state.
                    if (!tool.isGoodState(succState))
                    {
						synchronized (this) {
                            final int errorCode = EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT;
							if (this.setErrState(curState, succState, false, errorCode)) {
								final Set<OpDeclNode> unassigned = succState.getUnassigned();
								String[] parameters;
								if (tool.getActions().length == 1) {
									parameters = new String[] { unassigned.size() > 1 ? "s are" : " is",
											unassigned.stream().map(n -> n.getName().toString())
													.collect(Collectors.joining(", ")) };
								} else {
									parameters = new String[] { tool.getActions()[i].getName().toString(),
											unassigned.size() > 1 ? "s are" : " is",
											unassigned.stream().map(n -> n.getName().toString())
													.collect(Collectors.joining(", ")) };
								}
								this.printTrace(errorCode, parameters, curState, succState);
							}
						}
                        return allSuccNonLeaf;
                    }

                    boolean inModel = (tool.isInModel(succState) && tool.isInActions(curState, succState));
                    int status = FPIntSet.NEW;
                    if (inModel)
                    {
                        long fp = succState.fingerPrint();
                        status = this.theFPSet.setStatus(fp, FPIntSet.NEW);
                        allSuccDone = allSuccDone && FPIntSet.isDone(status);
                        allSuccNonLeaf = allSuccNonLeaf && !FPIntSet.isLeaf(status);

                        // Write out the state when new and asked:
                        this.allStateWriter.writeState(curState, succState, status == FPIntSet.NEW);

                        // Remember succState if it has not been completed at this level:
                        if (!FPIntSet.isCompleted(status))
                        {
                            states.addElement(succState);
                            fps.addElement(fp);
                        }

                        // For liveness checking:
                        if (this.checkLiveness && isLeaf)
                        {
                            liveNextStates.put(fp, succState);
                        }
                    }

                    // Check if the state violates any invariant:
                    if (status == FPIntSet.NEW)
                    {
                        try
                        {
                            int len = tool.getInvariants().length;
                            for (k = 0; k < len; k++)
                            {
                                if (!tool.isValid(tool.getInvariants()[k], succState))
                                {
                                    // We get here because of invariant violation:
                                    synchronized (this)
                                    {
                                        if (TLCGlobals.continuation)
                                        {
                                            this.printTrace(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR,
                                                    new String[] { tool.getInvNames()[k] }, curState, succState);
                                            break;
                                        } else
                                        {
                                            if (this.setErrState(curState, succState, false, EC.TLC_INVARIANT_VIOLATED_BEHAVIOR))
                                            {
                                                this.printTrace(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR,
                                                        new String[] { tool.getInvNames()[k] }, curState,
                                                        succState);
                                                this.notify();
                                            }
                                            return allSuccNonLeaf;
                                        }
                                    }
                                }
                            }
                            if (k < len)
                                continue;
                        } catch (Exception e)
                        {
                        	synchronized (this) {
		                        if (this.setErrState(curState, succState, true, EC.TLC_INVARIANT_EVALUATION_FAILED))
		                        {
		                            this.printTrace(EC.TLC_INVARIANT_EVALUATION_FAILED, new String[] { tool
		                                    .getInvNames()[k] }, curState, succState);
		                            this.notify();
		                        }
		                        return allSuccNonLeaf;
                        	}
                        }
                    }
                    // Check if the state violates any implied action. We need to do it
                    // even if succState is not new.
                    try
                    {
                        int len = tool.getImpliedActions().length;
                        for (k = 0; k < len; k++)
                        {
                            if (!tool.isValid(tool.getImpliedActions()[k], curState, succState))
                            {
                                // We get here because of implied-action violation:
                                synchronized (this)
                                {
                                    if (TLCGlobals.continuation)
                                    {
                                        this
                                                .printTrace(EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR,
                                                        new String[] { tool.getImpliedActNames()[k] }, curState,
                                                        succState);
                                        break;
                                    } else
                                    {
                                        if (this.setErrState(curState, succState, false, EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR))
                                        {
                                            this.printTrace(EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR,
                                                    new String[] { tool.getImpliedActNames()[k] }, curState,
                                                    succState);
                                            this.notify();
                                        }
                                        return allSuccNonLeaf;
                                    }
                                }
                            }
                        }
                        if (k < len)
                            continue;
                    } catch (Exception e)
                    {
                    	synchronized (this) {
		                    if (this.setErrState(curState, succState, true, EC.TLC_ACTION_PROPERTY_EVALUATION_FAILED))
		                    {
		                        this.printTrace(EC.TLC_ACTION_PROPERTY_EVALUATION_FAILED, new String[] { tool
		                                .getImpliedActNames()[k] }, curState, succState);
		                        this.notify();
		                    }
                    	}
                    	return allSuccNonLeaf;
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
                    if (this.setErrState(curState, null, false, EC.TLC_DEADLOCK_REACHED))
                    {
                        this.printTrace(EC.TLC_DEADLOCK_REACHED, null, curState, null);
                        this.notify();
                    }
                }
                return allSuccNonLeaf;
            }

            // Finally, add curState into the behavior graph for liveness checking:
            if (this.checkLiveness && isLeaf)
            {
            	final long curStateFP = curState.fingerPrint();
                // Add a stuttering step for curState:
                liveNextStates.put(curStateFP, curState);
            	this.allStateWriter.writeState(curState, curState, true, IStateWriter.Visualization.STUTTERING);
                // Add curState to the behavior graph:
                liveCheck.addNextState(tool, curState, curStateFP, liveNextStates);

				// Poor man's version of a controller. If necessary, try e.g.
				// PID controller instead.
				final int multiplier = threadLocal.get();
				if (liveNextStates.capacity() > (multiplier * INITIAL_CAPACITY)) {
					// Increase initial size for as long as the set has to grow
					threadLocal.set(multiplier + 1);
				}
            }

            // We set curState DONE if
            // o all of its children is already DONE, or
            // o it is a leaf state and none of its children is NEW.
            // Otherwise, set curState to NONELEAF.
            if (allSuccDone || (isLeaf && allSuccNonLeaf))
            {
                this.theFPSet.setStatus(cfp, FPIntSet.DONE);
            }
            return allSuccNonLeaf;
        } catch (Throwable e)
        {
            // Assert.printStack(e);
            boolean keep = ((e instanceof StackOverflowError) || (e instanceof OutOfMemoryError));
            synchronized (this)
            {
                final int errorCode;
                if (e instanceof StackOverflowError)
                {
                    errorCode = EC.SYSTEM_STACK_OVERFLOW;
                } else if (e instanceof OutOfMemoryError)
                {
                    errorCode = EC.SYSTEM_OUT_OF_MEMORY;
                } else
                {
                    errorCode = EC.GENERAL;
                }

                if (this.setErrState(curState, succState, !keep, errorCode))
                {
                    String[] parameters = null;
                    if (errorCode == EC.GENERAL)
                    {
                        // LL changed error message on 7 April 2012
                        parameters = new String[] { 
                                MP.ECGeneralMsg("computing the set of next states", e) }; 
                    }
                    this.printTrace(errorCode, parameters, curState, succState);
                    this.notifyAll();
                }
            }
            throw e;
        }
    }

    private final void printTrace(int errorCode, String[] parameters, TLCState s1, TLCState s2)
    {
    	if (EC.TLC_INVARIANT_VIOLATED_BEHAVIOR == errorCode)
    	{
			((DFIDWorker) this.workers[IdThread.GetId()]).printInvariantTrace(errorCode, parameters, s1, s2);
    	}
    	else
    	{
			((DFIDWorker) this.workers[IdThread.GetId()]).printErrorTrace(errorCode, parameters, s1, s2);
    	}
    }

    /**
     * Set the error state. 
     * <strong>Note:</note> this method must be protected by lock 
     */
    public boolean setErrState(TLCState curState, TLCState succState, boolean keep, int errorCode)
    {
        boolean result = super.setErrState(curState, succState, keep, errorCode);
        if (!result)
        {
            return false;
        } else
        {
            this.setStop(2);
            return true;
        }
    }

    /**
     * Stop the workers
     * @param code
     */
    public final void setStop(int code)
    {
        for (int i = 0; i < this.workers.length; i++)
        {
            ((DFIDWorker) this.workers[i]).setStop(code);
        }
    }

    /**
     * There are several things to do:
     * Check liveness: check liveness properties on the partial state graph.
     * Checkpoint: checkpoint three data structures: the state set, the
     *             state queue, and the state trace.
     */
    @Override
    public final int doPeriodicWork() throws Exception
    {
        synchronized (this.theFPSet)
        {
            // Run liveness checking, if needed:
            if (this.checkLiveness)
            {
                final int result = liveCheck.check(tool, false);
                if (result != EC.NO_ERROR)
                {
                    return result;
                }
            }

            if (TLCGlobals.doCheckPoint()) {
            	// Checkpoint:
            	MP.printMessage(EC.TLC_CHECKPOINT_START, this.metadir);
            	// start checkpointing:
            	this.theFPSet.beginChkpt();
            	if (this.checkLiveness)
            	{
            		liveCheck.beginChkpt();
            	}
            	UniqueString.internTbl.beginChkpt(this.metadir);
            	
            	// Commit checkpoint:
            	this.theFPSet.commitChkpt();
            	if (this.checkLiveness)
            	{
            		liveCheck.commitChkpt();
            	}
            	UniqueString.internTbl.commitChkpt(this.metadir);
            	MP.printMessage(EC.TLC_CHECKPOINT_END);
            }
        }
        return EC.NO_ERROR;
    }

    public final boolean recover() throws IOException
    {
        boolean recovered = false;
        if (this.fromChkpt != null)
        {
            // We recover from previous checkpoint.
            MP.printMessage(EC.TLC_CHECKPOINT_RECOVER_START, this.fromChkpt);
            this.theFPSet.recover();
            if (this.checkLiveness)
            {
                liveCheck.recover();
            }
            MP.printMessage(EC.TLC_CHECKPOINT_RECOVER_END_DFID, String.valueOf(this.theFPSet.size()));
            recovered = true;
            this.numOfGenStates.set(this.theFPSet.size());
        }
        return recovered;
    }

    protected final void cleanup(boolean success) throws IOException
    {
        this.theFPSet.close();
        if (this.checkLiveness)
            liveCheck.close();
        this.allStateWriter.close();
        // SZ Feb 23, 2009:
        // FileUtil.deleteDir(new File(this.metadir), success);
        FileUtil.deleteDir(this.metadir, success);
    }

    public final void printSummary(boolean success) throws IOException
    {
        this.reportCoverage(this.workers);

        /*
         * This allows the toolbox to easily display the last set
         * of state space statistics by putting them in the same
         * form as all other progress statistics.
         */
        if (TLCGlobals.tool)
        {
            MP.printMessage(EC.TLC_PROGRESS_STATS_DFID, new String[] { String.valueOf(this.numOfGenStates),
                    String.valueOf(this.theFPSet.size()) });
        }

        MP.printMessage(EC.TLC_STATS_DFID, new String[] { String.valueOf(this.numOfGenStates),
                String.valueOf(this.theFPSet.size()) });
    }

    private final void reportSuccess() throws IOException
    {
        reportSuccess(this.theFPSet.size(), this.theFPSet.checkFPs(), numOfGenStates.get());
    }

    /**
     * Create workers
     */
    protected IWorker[] startWorkers(AbstractChecker checker, int checkIndex)
    {
        for (int i = 0; i < this.workers.length; i++)
        {
            this.workers[i] = new DFIDWorker(i, checkIndex, checker);
        }
		// Start all workers once instantiated to avoid a race with setStop,
		// when setStop is being called concurrently with startWorkers. This
		// happens, if a DFIDWorker terminates immediately.
        for (int i = 0; i < this.workers.length; i++)
        {
            this.workers[i].start();
        }
        return this.workers;
    }

    /**
     * Process calculation 
     * @param count
     * @param depth
     * @throws Exception
     */
    protected void runTLCContinueDoing(int count, int depth) throws Exception
    {
        MP.printMessage(EC.TLC_PROGRESS_STATS_DFID, new String[] { String.valueOf(this.numOfGenStates),
                String.valueOf(this.theFPSet.size()) });
        if (count == 0)
        {
            this.reportCoverage(this.workers);
            count = TLCGlobals.coverageInterval / TLCGlobals.progressInterval;
        } else
        {
            count--;
        }
        this.wait(TLCGlobals.progressInterval);
    }

}