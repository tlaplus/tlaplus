// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tlc2.tool;

import java.io.IOException;
import java.util.concurrent.atomic.AtomicLong;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ExprNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.fp.dfid.FPIntSet;
import tlc2.tool.fp.dfid.MemFPIntSet;
import tlc2.tool.liveness.LiveCheck;
import tlc2.tool.liveness.LiveException;
import tlc2.util.IdThread;
import tlc2.util.LongVec;
import tlc2.util.ObjLongTable;
import util.FileUtil;
import util.FilenameToStream;
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
    protected DFIDWorker[] workers; // the workers

    /** 
     * Constructor for running DFID   
     * @param resolver 
     */
    public DFIDModelChecker(String specFile, String configFile, String dumpFile, boolean deadlock, String fromChkpt,
            boolean preprocess, FilenameToStream resolver, SpecObj specObj) throws EvalException, IOException
    {
        // call the abstract constructor
        super(specFile, configFile, dumpFile, deadlock, fromChkpt, preprocess, resolver, specObj);

        this.theInitStates = null;
        this.theInitFPs = null;
        this.theFPSet = new MemFPIntSet(); // init the state set
        this.theFPSet.init(TLCGlobals.getNumWorkers(), this.metadir, specFile);

        // Initialize all the workers:
        this.workers = new DFIDWorker[TLCGlobals.getNumWorkers()];
    }

    /**
     * This method does model checking on a TLA+ spec. All the visited
     * states are stored in the variable theFPSet.
     */
    public void modelCheck() throws Exception
    {
        // Initialization for liveness checking:
        if (this.checkLiveness)
        {
            LiveCheck.init(this.tool, this.actions, this.metadir);
        }

        boolean recovered = this.recover();
        try
        {
            if (!this.checkAssumptions())
                return;
            if (!this.doInit(false))
                return;
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
            this.tool.setCallStack();
            try
            {
                this.numOfGenStates = new AtomicLong(0);
                this.doInit(true);
            } catch (Throwable e1)
            {
                MP.printError(EC.TLC_NESTED_EXPRESSION, this.tool.getCallStack().toString());
            }
            this.printSummary(false);
            this.cleanup(false);
            return;
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
        if (this.actions.length == 0)
        {
            this.reportSuccess();
            this.printSummary(true);
            this.cleanup(true);
            return;
        }

        boolean success = false;
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
                            MP.printMessage(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete");
                            // SZ Jul 10, 2009: what for?
                            // ToolIO.out.flush();
                            success = LiveCheck.check();
                            if (!success)
                                return;
                        }

                        // We get here because the checking has been completed.
                        success = true;
                        this.reportSuccess();
                    } else if (this.keepCallStack)
                    {
                        // Replay the error with the error stack recorded:
                        this.tool.setCallStack();
                        try
                        {
                            this.doNext(this.predErrState, this.predErrState.fingerPrint(), true, new ObjLongTable(10),
                                    new StateVec(1), new LongVec());
                        } catch (Throwable e)
                        {
                            MP.printError(EC.TLC_NESTED_EXPRESSION, this.tool.getCallStack().toString());
                        }
                    }
                    break;
                }

                // Start working on this level:
                MP.printMessage(EC.TLC_PROGRESS_STATS_DFID, new String[] { String.valueOf(level),
                        String.valueOf(this.numOfGenStates), String.valueOf(this.theFPSet.size()) });

                FPIntSet.incLevel();
                success = this.runTLC(level);
                if (!success)
                    return;

                // Check if we should stop at this level:
                for (int i = 0; i < this.workers.length; i++)
                {
                    if (this.workers[i].isTerminated())
                    {
                        terminated = true;
                        break;
                    }
                }
                boolean moreLevel = false;
                for (int i = 0; i < this.workers.length; i++)
                {
                    if (this.workers[i].hasMoreLevel())
                    {
                        moreLevel = true;
                        break;
                    }
                }
                terminated = terminated || !moreLevel;
            }
        } catch (Exception e)
        {
            // Assert.printStack(e);
            success = false;
            if (!(e instanceof LiveException))
            {
                MP.printError(EC.GENERAL, e);  // LL changed call 7 April 2012
            }
        } finally
        {
            this.printSummary(success);
            this.cleanup(success);
        }
    }

    /* Check the assumptions.  
     * This code is a clone of the same method in ModelChecker */
    public final boolean checkAssumptions()
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

    /* Compute the set of initial states.  */
    // SZ Feb 23, 2009: added ignore cancel flag
    public final boolean doInit(boolean ignoreCancel) throws Throwable
    {
        TLCState curState = null;
        try
        {
            // Generate the initial states:
            StateVec states = this.tool.getInitStates();
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
                if (!this.tool.isGoodState(curState))
                {
                    MP.printError(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_INITIAL, curState.toString());
                    return false;
                }
                boolean inModel = this.tool.isInModel(curState);
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
                        if (this.allStateWriter != null)
                        {
                            this.allStateWriter.writeState(curState);
                        }

                        // build behavior graph for liveness checking
                        if (this.checkLiveness)
                        {
                            LiveCheck.addInitState(curState, fp);
                        }
                    }
                }
                // Check properties of the state:
                if (status == FPIntSet.NEW)
                {
                    for (int j = 0; j < this.invariants.length; j++)
                    {
                        if (!this.tool.isValid(this.invariants[j], curState))
                        {
                            // We get here because of invariant violation:
                            MP.printError(EC.TLC_INVARIANT_VIOLATED_INITIAL, new String[] { this.tool.getInvNames()[j],
                                    curState.toString() });
                            if (!TLCGlobals.continuation)
                                return false;
                        }
                    }
                    for (int j = 0; j < this.impliedInits.length; j++)
                    {
                        if (!this.tool.isValid(this.impliedInits[j], curState))
                        {
                            // We get here because of implied-inits violation:
                            MP.printError(EC.TLC_PROPERTY_VIOLATED_INITIAL, new String[] {
                                    this.tool.getImpliedInitNames()[j], curState.toString() });
                            return false;
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
                MP.printError(EC.SYSTEM_OUT_OF_MEMORY_TOO_MANY_INIT);
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
    public final boolean doNext(TLCState curState, long cfp, boolean isLeaf, ObjLongTable counts, StateVec states,
            LongVec fps) throws Throwable
    {
        boolean deadLocked = true;
        TLCState succState = null;
        StateVec liveNextStates = null;
        LongVec liveNextFPs = null;

        if (this.checkLiveness && isLeaf)
        {
            liveNextStates = new StateVec(2);
            liveNextFPs = new LongVec(2);
        }

        try
        {
            int k = 0;
            boolean allSuccDone = true;
            boolean allSuccNonLeaf = true;
            for (int i = 0; i < this.actions.length; i++)
            {
                StateVec nextStates = this.tool.getNextStates(this.actions[i], curState);
                int sz = nextStates.size();
                this.incNumOfGenStates(sz);
                deadLocked = deadLocked && (sz == 0);

                for (int j = 0; j < sz; j++)
                {
                    succState = nextStates.elementAt(j);
                    // Check if the state is a legal state.
                    if (!this.tool.isGoodState(succState))
                    {
                        if (this.setErrState(curState, succState, false))
                        {
                            this.printTrace(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT, null, curState, succState);

                            synchronized (this)
                            {
                                this.notify();
                            }
                        }
                        return allSuccNonLeaf;
                    }

                    if (TLCGlobals.coverageInterval >= 0)
                    {
                        ((TLCStateMutSource) succState).addCounts(counts);
                    }

                    boolean inModel = (this.tool.isInModel(succState) && this.tool.isInActions(curState, succState));
                    int status = FPIntSet.NEW;
                    if (inModel)
                    {
                        long fp = succState.fingerPrint();
                        status = this.theFPSet.setStatus(fp, FPIntSet.NEW);
                        allSuccDone = allSuccDone && FPIntSet.isDone(status);
                        allSuccNonLeaf = allSuccNonLeaf && !FPIntSet.isLeaf(status);

                        // Write out the state when new and asked:
                        if (status == FPIntSet.NEW && this.allStateWriter != null)
                        {
                            this.allStateWriter.writeState(succState);
                        }

                        // Remember succState if it has not been completed at this level:
                        if (!FPIntSet.isCompleted(status))
                        {
                            states.addElement(succState);
                            fps.addElement(fp);
                        }

                        // For liveness checking:
                        if (this.checkLiveness && isLeaf)
                        {
                            liveNextStates.addElement(succState);
                            liveNextFPs.addElement(fp);
                        }
                    }

                    // Check if the state violates any invariant:
                    if (status == FPIntSet.NEW)
                    {
                        try
                        {
                            int len = this.invariants.length;
                            for (k = 0; k < len; k++)
                            {
                                if (!tool.isValid(this.invariants[k], succState))
                                {
                                    // We get here because of invariant violation:
                                    synchronized (this)
                                    {
                                        if (TLCGlobals.continuation)
                                        {
                                            this.printTrace(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR,
                                                    new String[] { this.tool.getInvNames()[k] }, curState, succState);
                                            break;
                                        } else
                                        {
                                            if (this.setErrState(curState, succState, false))
                                            {
                                                this.printTrace(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR,
                                                        new String[] { this.tool.getInvNames()[k] }, curState,
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
                            if (this.setErrState(curState, succState, true))
                            {
                                this.printTrace(EC.TLC_INVARIANT_EVALUATION_FAILED, new String[] { this.tool
                                        .getInvNames()[k] }, curState, succState);
                                this.notify();
                            }
                            return allSuccNonLeaf;
                        }
                    }
                    // Check if the state violates any implied action. We need to do it
                    // even if succState is not new.
                    try
                    {
                        int len = this.impliedActions.length;
                        for (k = 0; k < len; k++)
                        {
                            if (!tool.isValid(this.impliedActions[k], curState, succState))
                            {
                                // We get here because of implied-action violation:
                                synchronized (this)
                                {
                                    if (TLCGlobals.continuation)
                                    {
                                        this
                                                .printTrace(EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR,
                                                        new String[] { this.tool.getImpliedActNames()[k] }, curState,
                                                        succState);
                                        break;
                                    } else
                                    {
                                        if (this.setErrState(curState, succState, false))
                                        {

                                            this.printTrace(EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR,
                                                    new String[] { this.tool.getImpliedActNames()[k] }, curState,
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
                        if (this.setErrState(curState, succState, true))
                        {
                            this.printTrace(EC.TLC_ACTION_PROPERTY_EVALUATION_FAILED, new String[] { this.tool
                                    .getImpliedActNames()[k] }, curState, succState);
                            this.notify();
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
                    if (this.setErrState(curState, null, false))
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
                // Add a stuttering step for curState:
                long curStateFP = curState.fingerPrint();
                liveNextStates.addElement(curState);
                liveNextFPs.addElement(curStateFP);
                // Add curState to the behavior graph:
                LiveCheck.addNextState(curState, curStateFP, liveNextStates, liveNextFPs);
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
                if (this.setErrState(curState, succState, !keep))
                {
                    String[] parameters = null;
                    int errorCode;
                    if (e instanceof StackOverflowError)
                    {
                        errorCode = EC.SYSTEM_STACK_OVERFLOW;
                    } else if (e instanceof OutOfMemoryError)
                    {
                        errorCode = EC.SYSTEM_OUT_OF_MEMORY;
                    } else
                    {
                        errorCode = EC.GENERAL;
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
        this.workers[IdThread.GetId()].printTrace(errorCode, parameters, s1, s2);
    }

    /**
     * Set the error state. 
     * <strong>Note:</note> this method must be protected by lock 
     */
    public boolean setErrState(TLCState curState, TLCState succState, boolean keep)
    {
        boolean result = super.setErrState(curState, succState, keep);
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
            this.workers[i].setStop(code);
        }
    }

    /**
     * There are several things to do:
     * Check liveness: check liveness properties on the partial state graph.
     * Checkpoint: checkpoint three data structures: the state set, the
     *             state queue, and the state trace.
     */
    public final boolean doPeriodicWork() throws Exception
    {
        synchronized (this.theFPSet)
        {
            // Run liveness checking, if needed:
            long stateNum = this.theFPSet.size();
            boolean doCheck = this.checkLiveness && (stateNum >= nextLiveCheck);
            if (doCheck)
            {
                MP.printMessage(EC.TLC_CHECKING_TEMPORAL_PROPS, "current");
                if (!LiveCheck.check())
                {
                    return false;
                }
                nextLiveCheck = (stateNum < 600000) ? stateNum * 2 : stateNum + 200000;
            }

            // Checkpoint:
            MP.printMessage(EC.TLC_CHECKPOINT_START, this.metadir);
            // start checkpointing:
            this.theFPSet.beginChkpt();
            if (this.checkLiveness)
            {
                LiveCheck.beginChkpt();
            }
            UniqueString.internTbl.beginChkpt(this.metadir);

            // Commit checkpoint:
            this.theFPSet.commitChkpt();
            if (this.checkLiveness)
            {
                LiveCheck.commitChkpt();
            }
            UniqueString.internTbl.commitChkpt(this.metadir);
            MP.printMessage(EC.TLC_CHECKPOINT_END);
        }
        return true;
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
                LiveCheck.recover();
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
            LiveCheck.close();
        if (this.allStateWriter != null)
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

    public final void reportSuccess() throws IOException
    {
        long d = this.theFPSet.size();
        double prob1 = (d * (this.numOfGenStates.get() - d)) / Math.pow(2, 64);
        double prob2 = this.theFPSet.checkFPs();

        MP.printMessage(EC.TLC_SUCCESS, new String[] { String.valueOf(prob1), String.valueOf(prob2) });
    }

    /**
     * Create workers
     */
    protected IdThread[] startWorkers(AbstractChecker checker, int checkIndex)
    {
        for (int i = 0; i < this.workers.length; i++)
        {
            this.workers[i] = new DFIDWorker(i, checkIndex, checker);
            this.workers[i].start();
        }
        return this.workers;
    }

    /**
     * Run prior the worker loop
     */
    protected void runTLCPreLoop()
    {
        this.done = false;
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