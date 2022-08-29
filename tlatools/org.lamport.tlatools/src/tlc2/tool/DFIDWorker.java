// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tlc2.tool;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.output.StatePrinter;
import tlc2.tool.fp.dfid.FPIntSet;
import tlc2.tool.impl.Tool;
import tlc2.util.IdThread;
import tlc2.util.LongVec;
import tlc2.util.RandomGenerator;

public class DFIDWorker extends IdThread implements IWorker {
    /**
     * Multi-threading helps only when running on multiprocessors. TLC
     * can pretty much eat up all the cycles of a processor running
     * single threaded.  We expect to get linear speedup with respect
     * to the number of processors.
     */
    private final DFIDModelChecker tlc;
    private final RandomGenerator rng;
    private final TLCState[] stateStack;
    private final long[] fpStack;
    private final StateVec[] succStateStack;
    private final LongVec[] succFPStack;
    private final FPIntSet theFPSet;
    private final TLCState[] theInitStates;
    private final long[] theInitFPs;
    private final int toLevel;
    private int initLen;
    private int curLevel;
    private int stopCode;
    private boolean moreLevel;

    // SZ Feb 20, 2009: changes due to the introduced super type
    public DFIDWorker(final int id, final int toLevel, final AbstractChecker tlc) {
        super(id);
        this.tlc = (DFIDModelChecker) tlc;
        this.rng = new RandomGenerator();
        this.rng.setSeed(this.rng.nextLong());

        int dfidMax = this.tlc.dfidMax;

        this.stateStack = new TLCState[dfidMax];
        this.fpStack = new long[dfidMax];
        this.succStateStack = new StateVec[dfidMax];
        this.succFPStack = new LongVec[dfidMax];
        for (int i = 0; i < dfidMax; i++) {
            this.succStateStack[i] = new StateVec(1);
            this.succFPStack[i] = new LongVec(1);
        }
        this.theFPSet = this.tlc.theFPSet;
        this.initLen = this.tlc.theInitStates.length;
        this.theInitStates = new TLCState[this.initLen];
        this.theInitFPs = new long[this.initLen];
        System.arraycopy(this.tlc.theInitStates, 0, this.theInitStates, 0, this.initLen);
        System.arraycopy(this.tlc.theInitFPs, 0, this.theInitFPs, 0, this.initLen);
        this.toLevel = toLevel;
        this.curLevel = 0;
        this.stopCode = 0;
        this.moreLevel = false;
    }

    public final void setStop(final int code) {
        this.stopCode = code;
    }

    public final boolean isTerminated() {
        return this.stopCode == 2;
    }

    public final boolean hasMoreLevel() {
        return this.moreLevel;
    }

    /**
     * Choose a random initial state that has not been done. Return the
     * index of the chosen state. Return -1 if there is no such kind of
     * initial state.
     */
    private int getInit() {
        while (this.initLen > 0) {
            final int index = (int) Math.floor(this.rng.nextDouble() * this.initLen);
            final long fp = this.theInitFPs[index];
            final int status = this.theFPSet.getStatus(fp);

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
    private int getNext(final TLCState curState, final long cfp) {
        final StateVec succStates = this.succStateStack[this.curLevel - 1];
        final LongVec succFPs = this.succFPStack[this.curLevel - 1];
        int len = succFPs.size();

        while (len > 0) {
            final int index = (int) Math.floor(this.rng.nextDouble() * len);
            final long fp = succFPs.get(index);
            final int status = this.theFPSet.getStatus(fp);

            // Assert.check(status != FPIntSet.NEW);
            if (!FPIntSet.isCompleted(status) &&
                    this.curLevel < FPIntSet.getLevel(status)) {
                return index;
            }

            succStates.removeIndexMovingLastElement(index);
            succFPs.removeIndexMovingLastElement(index);
            len--;
        }
        return -1;
    }

    /**
     * Prints the stacktrace
     */
    public final void printErrorTrace(final int errorCode, final String[] parameters, final TLCState s1, final TLCState s2) {
        MP.printError(errorCode, parameters);
        MP.printError(EC.TLC_BEHAVIOR_UP_TO_THIS_POINT);
        int idx = 0;
        while (idx < this.curLevel) {
            StatePrinter.printRuntimeErrorStateTraceState(this.stateStack[idx], ++idx);
        }
        // the prefix printed by the while loop should end at s1.
        assert s1.equals(this.stateStack[idx]);
        StatePrinter.printRuntimeErrorStateTraceState(s1, ++idx);
        if (s2 != null) {
            StatePrinter.printRuntimeErrorStateTraceState(s2, idx + 1);
        }
    }

    /**
     * Prints the state trace when an invariant fails.
     *
     * @param errorCode  Error code identifying type of failure.
     * @param parameters Error detail.
     * @param s1         Predecessor state to state which fails to satisfy invariant.
     * @param s2         State which fails to satisfy invariant.
     */
    public final void printInvariantTrace(final int errorCode, final String[] parameters, final TLCState s1, final TLCState s2) {
        MP.printError(errorCode, parameters);
        MP.printError(EC.TLC_BEHAVIOR_UP_TO_THIS_POINT);
        int idx = 0;
        for (; idx <= this.curLevel; idx++) {
            assert this.curLevel != idx || s1.equals(this.stateStack[idx]);

            final int ordinal = idx + 1;
            final TLCStateInfo currentState = new TLCStateInfo(this.stateStack[idx], ordinal);
            final TLCState previousState = 0 == idx ? null : this.stateStack[idx - 1];
            StatePrinter.printInvariantViolationStateTraceState(currentState, previousState, ordinal);
        }

        final int ordinal = idx + 1;
        final TLCStateInfo currentState = new TLCStateInfo(s2, ordinal);
        StatePrinter.printInvariantViolationStateTraceState(currentState, s1, ordinal);
    }

    /* This method does a depth-first search up to the depth of toLevel. */
    @Override
    public final void run() {
        TLCState curState = null;
        setUsingModelChecker(Tool.Mode.Executor);
        setMainChecker(this.tlc);

        try {
            while (this.stopCode == 0) {
                // Choose a random initial state and compute its successors:
                int index = this.getInit();
                if (index == -1) {
                    this.tlc.setStop(1);
                    synchronized (this.tlc) {
                        this.tlc.setDone();
                        this.tlc.notifyAll();
                    }
                    return;
                }

                curState = this.theInitStates[index];
                long cfp = this.theInitFPs[index];
                this.stateStack[0] = curState;
                this.fpStack[0] = cfp;
                this.succStateStack[0].clear();
                this.succFPStack[0].clear();
                boolean isLeaf = this.toLevel < 2;
                boolean noLeaf = this.tlc.doNext(curState, cfp, isLeaf,
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
                        curState = this.stateStack[this.curLevel - 1];
                        cfp = this.fpStack[this.curLevel - 1];
                    } else {
                        curState = this.succStateStack[this.curLevel - 1].get(index);
                        cfp = this.succFPStack[this.curLevel - 1].get(index);
                        this.stateStack[this.curLevel] = curState;
                        this.fpStack[this.curLevel] = cfp;
                        this.succStateStack[this.curLevel].clear();
                        this.succFPStack[this.curLevel].clear();
                        isLeaf = (this.curLevel >= this.toLevel - 1);
                        noLeaf = this.tlc.doNext(curState, cfp, isLeaf,
                                this.succStateStack[this.curLevel],
                                this.succFPStack[this.curLevel]);
                        this.moreLevel = this.moreLevel || !noLeaf;
                        this.curLevel++;
                    }
                }
            }
        } catch (final Throwable e) {
            // Something bad happened. Quit...
            // Assert.printStack(e);
            this.tlc.setStop(2);
            synchronized (this.tlc) {
                if (this.tlc.setErrState(curState, null, true, EC.GENERAL)) {
                    MP.printError(EC.GENERAL, e);  // LL changed call 7 April 2012
                }
                this.tlc.setDone();
                this.tlc.notifyAll();
            }
        }
    }

}
