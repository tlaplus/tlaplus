package tlc2.tool;

import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.module.TLCGetSet;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.coverage.CostModelCreator;
import tlc2.tool.liveness.*;
import tlc2.util.FP64;
import tlc2.util.IStateWriter;
import tlc2.util.IdThread;
import tlc2.util.statistics.ConcurrentBucketStatistics;
import tlc2.util.statistics.DummyBucketStatistics;
import tlc2.util.statistics.IBucketStatistics;
import tlc2.value.IValue;
import tlc2.value.RandomEnumerableValues;
import tlc2.value.impl.*;
import util.DebugPrinter;
import util.UniqueString;

import java.io.IOException;
import java.math.BigDecimal;
import java.math.MathContext;
import java.util.*;

/**
 * The abstract checker
 *
 * @author Simon Zambrovski
 */
public abstract class AbstractChecker {
    protected static final boolean LIVENESS_STATS = Boolean.getBoolean(Liveness.class.getPackage().getName() + ".statistics");
    /**
     * True when unit tests explicitly request to use
     * {@link AddAndCheckLiveCheck} to run liveness checking after each
     * insertion into the behavior graph. This should only be true if you
     * exactly know what you are doing. If you don't and this is true, make sure
     * it's false.
     */
    public static boolean LIVENESS_TESTING_IMPLEMENTATION = Boolean.getBoolean(ILiveCheck.class.getName() + ".testing");
    private static long lastChkpt = System.currentTimeMillis();
    public final String metadir;
    public final ITool tool;
    protected final boolean checkDeadlock;
    protected final boolean checkLiveness;
    protected final String fromChkpt;
    protected final IStateWriter allStateWriter;
    protected final ILiveCheck liveCheck;
    /**
     * Timestamp of when model checking started.
     */
    protected final long startTime;
    private final Value config;
    protected TLCState predErrState;
    protected TLCState errState;
    protected int errorCode;
    protected boolean done;
    protected boolean keepCallStack;
    protected IWorker[] workers;
    protected Timer terminationTimer;

    /**
     * Constructor of the abstract model checker
     */
    public AbstractChecker(final ITool tool, final String metadir, final IStateWriter stateWriter,
                           final boolean deadlock, final String fromChkpt, final long startTime) throws EvalException, IOException {
        this.tool = tool;

        this.checkDeadlock = deadlock;
        this.checkLiveness = !this.tool.livenessIsTrue();

        // moved to file utilities
        this.metadir = metadir;

        this.errState = null;
        this.predErrState = null;
        this.done = false;
        this.errorCode = EC.NO_ERROR;
        this.keepCallStack = false;

        this.fromChkpt = fromChkpt;

        this.allStateWriter = stateWriter;

        this.startTime = startTime;

        if (TLCGlobals.isCoverageEnabled()) {
            CostModelCreator.create(this.tool);
        }

        if (this.checkLiveness) {
            if (tool.hasSymmetry()) {
                // raise warning...
                MP.printWarning(EC.TLC_FEATURE_UNSUPPORTED_LIVENESS_SYMMETRY);
            }
            // LL: "[this message is] rather silly because it can obviously also cause TLC
            // to fail to find violations of a safety property. I suggest removing that
            // warning.
            // Also see org.lamport.tla.toolbox.tool.tlc.ui.editor.page.advanced.AdvancedModelPage.validatePage(boolean)
//        	if (tool.hasStateOrActionConstraints()) {
//				MP.printWarning(EC.TLC_FEATURE_LIVENESS_CONSTRAINTS);
//        	}
            // Initialization for liveness checking:
            report("initializing liveness checking");
            IBucketStatistics stats = new DummyBucketStatistics();
            if (LIVENESS_STATS) {
                stats = new ConcurrentBucketStatistics("Histogram vertex out-degree", LiveCheck.class.getPackage().getName(),
                        "DiskGraphsOutDegree");
            }
            if (LIVENESS_TESTING_IMPLEMENTATION) {
                this.liveCheck = new AddAndCheckLiveCheck(this.tool, this.metadir, stats);
            } else {
                this.liveCheck = new LiveCheck(this.tool, this.metadir, stats, stateWriter);
            }
            report("liveness checking initialized");
        } else {
            this.liveCheck = new NoOpLiveCheck(this.tool, this.metadir);
        }

        // Eagerly create the config value in case the next-state relation involves
        // TLCGet("config"). In this case, we would end up locking the
        // UniqueString#InternTable for every lookup. See Simulator too.
        this.config = createConfig();

        terminationTimer = scheduleTermination(new TimerTask() {
            @Override
            public void run() {
                try {
                    AbstractChecker.this.stop();
                } catch (Exception e) {
                }
            }
        });
    }

    /**
     * IMPORTANT NOTE: The method is unsynchronized. It is the caller's
     * responsibility to ensure that only a single thread calls this method.
     *
     * @return true iff a checkpoint should be created next time possible
     */
    public static boolean doCheckPoint() {
        // 1. checkpoint forced externally (e.g. JMX)
        if (TLCGlobals.forceChkpt) {
            TLCGlobals.forceChkpt = false;
            return true;
        }

        // 2. user has disabled checkpoints
        if (TLCGlobals.chkptDuration == 0) {
            return false;
        }

        // 3. time between checkpoints is up?
        final long now = System.currentTimeMillis();
        if (now - lastChkpt >= TLCGlobals.chkptDuration) {
            lastChkpt = now;
            return true;
        }
        return false;
    }

    public static double calculateOptimisticProbability(final long numOfDistinctStates, final long numOfGenStates) {
        return numOfDistinctStates * ((numOfGenStates - numOfDistinctStates) / Math.pow(2, 64));
    }

    public static void reportSuccess(final long numOfDistinctStates, final long numOfGenStates) {
        final double optimisticProb = calculateOptimisticProbability(numOfDistinctStates, numOfGenStates);
        MP.printMessage(EC.TLC_SUCCESS, new String[]{"val = " + ProbabilityToString(optimisticProb, 2)});
    }

    public static void reportSuccess(final long numOfDistinctStates, final long actualDistance,
                                     final long numOfGenStates) {
        // Prevent div-by-zero when calculating collision probabilities when no states
        // are generated.
        if (numOfDistinctStates == numOfGenStates && numOfGenStates == 0) {
            // When the number of states is zero, printing a collision probability is
            // useless anyway. But the Toolbox will probably crash if omitted.
            MP.printMessage(EC.TLC_SUCCESS, "val = 0.0", "val = 0.0");
            return;
        }
        // shown as 'calculated' in Toolbox
        final String optimisticProbStr = "val = "
                + ProbabilityToString(calculateOptimisticProbability(numOfDistinctStates, numOfGenStates), 2);

        // shown as 'observed' in Toolbox
        final BigDecimal actualProb = BigDecimal.valueOf(1d).divide(BigDecimal.valueOf(actualDistance),
                new MathContext(2));
        final String actualProbStr = "val = " + ProbabilityToString(actualProb.doubleValue(), 2);
        MP.printMessage(EC.TLC_SUCCESS, optimisticProbStr, actualProbStr);
    }

    /**
     * This method added by LL on 17 April 2012 to replace the use of the PrintfFormat
     * method in reportSuccess.
     * <p>
     * Returns a string representing the decimal representation of a probability to
     * a given number of significant digits.  If the input is not a probability, or if
     * some error is found, then it returns the result of applying Double.toString(long)
     * to the value.
     * <p>
     * Warning: the code makes the following assumption:
     * - Double.toString(v) returns a decimal representation of v of the
     * form  [d]* ["." [d]+ ["E" [+ | -] [d]+]  where d is a decimal digit and
     * [x]   = 0 or 1 instance of x
     * [x]*  = any number of instances of x
     * [x]+  = any non-zero number of instances of x
     * x | y = an x or a y
     *
     * @param val               - the probability represented as a long; must satisfy 0 <= val <= 1.
     * @param significantDigits - the number of significant digits to include; must be > 0.
     */
    private static String ProbabilityToString(final double val, final int significantDigits) {
        /*
         * If val = 0 (which shouldn't happen), return "0.0"
         */
        if (val == 0) {
            return "0.0";
        }

        final String valString = Double.toString(val);
        final int valStringLen = valString.length();

        StringBuilder result = new StringBuilder();
        int next = 0; // pointer to the next character in valString to examine.
        int significantDigitsFound = 0;

        /*
         * Skip past leading zeros.
         */
        while ((next < valStringLen) && (valString.charAt(next) == '0')) {
            next++;
        }

        /*
         * Append all the following digits to result, incrementing
         * significantDigits for each one.
         */
        while ((next < valStringLen) &&
                Character.isDigit(valString.charAt(next))) {
            result.append(valString.charAt(next));
            significantDigitsFound++;
            next++;
        }

        /*
         * IF next character is not "."
         *   THEN IF at end THEN return result
         *                  ELSE return valString.
         */
        if (next == valStringLen) {
            return result.toString();
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
            next++;
        } else {
            next++;
            result.append(".");
            if (significantDigitsFound == 0) {
                while ((next < valStringLen) && (valString.charAt(next) == '0')) {
                    next++;
                    result.append("0");
                }
            }
            while ((next < valStringLen) &&
                    Character.isDigit(valString.charAt(next)) &&
                    significantDigitsFound < significantDigits) {
                result.append(valString.charAt(next));
                next++;
                significantDigitsFound++;
            }
            if ((next < valStringLen) &&
                    Character.isDigit(valString.charAt(next)) &&
                    Character.digit(valString.charAt(next), 10) >= 5) {
                int prev = result.length() - 1; // the next digit of result to increment
                boolean done = false;
                while (!done) {
                    if (prev < 0) {
                        result.insert(0, "1");
                        done = true;
                    } else {
                        final char prevChar = result.charAt(prev);
                        final String front = result.substring(0, prev);
                        final String back = result.substring(prev + 1);
                        if (Character.isDigit(prevChar)) {
                            if (prevChar == '9') {
                                result = new StringBuilder(front + '0' + back);
                            } else {
                                result = new StringBuilder(front + Character.forDigit(Character.digit(prevChar, 10) + 1, 10) + back);
                                done = true;
                            }

                        }  // prevChar must be '.', so just continue

                    }
                    prev--;
                }
            }
        }
        while ((next < valStringLen) &&
                Character.isDigit(valString.charAt(next))) {
            next++;
        }

        /*
         * IF next at end of valString or at "E"
         *   THEN copy remaining chars of valString to result;
         *        return result
         *   ELSE return valString
         */
        if (next >= valStringLen) {
            return result.toString();
        }
        if (valString.charAt(next) == 'E') {
            next++;
            result.append("E");
            while (next < valStringLen) {
                result.append(valString.charAt(next));
                next++;
            }
            return result.toString();
        }
        return valString;
    }

    static Timer scheduleTermination(final TimerTask tt) {
        // Stops model checker after the given time in seconds. If model checking
        // terminates before stopAfter seconds, the timer task will never run.
        // Contrary to TLCSet("exit",...) this does not require a spec modification. Is
        // is likely of little use for regular TLC users. In other words, this is meant
        // to be a developer only feature and thus configured via a system property and
        // not a regular TLC parameter.
        final long stopAfter = Long.getLong(TLC.class.getName() + ".stopAfter", -1L);
        if (stopAfter > 0) {
            final Timer stopTimer = new Timer("TLCStopAfterTimer");
            stopTimer.schedule(tt, stopAfter * 1000L); // seconds to milliseconds.
            return stopTimer;
        }

        return null;
    }

    public void stop() throws Exception {
        if (Objects.nonNull(terminationTimer)) {
            terminationTimer.cancel();
            terminationTimer = null;
        }

    }

    public final boolean setDone() {
        final boolean old = this.done;
        this.done = true;
        return old;
    }

    /**
     * Set the error state.
     * <strong>Note:</note> this method must be protected by lock
     */
    public boolean setErrState(final TLCState curState, final TLCState succState, final boolean keepCallStack, final int errorCode) {
        assert Thread.holdsLock(this) : "Caller thread has to hold monitor!";
        if (!TLCGlobals.continuation && this.done)
            return false;
        IdThread.resetCurrentState();
        this.predErrState = curState;
        this.errState = (succState == null) ? curState : succState;
        this.errorCode = errorCode;
        this.done = true;
        this.keepCallStack = keepCallStack;
        return true;
    }

    public void setError(final boolean keepCallStack, final int errorCode) {
        assert Thread.holdsLock(this) : "Caller thread has to hold monitor!";
        IdThread.resetCurrentState();
        this.errorCode = errorCode;
        this.done = true;
        this.keepCallStack = keepCallStack;
    }

// The following method used for testing ProbabilityToString

    /**
     * Responsible for printing the coverage information
     */
    protected void reportCoverage(final IWorker[] workers) {
        // Without actions (empty spec) there won't be any statistics anyway.
        if (TLCGlobals.isCoverageEnabled() && this.tool.getActions().length > 0) {
            CostModelCreator.report(this.tool, this.startTime);
        }
    }

    /**
     * Initialize the model checker
     *
     * @return an error code, or <code>EC.NO_ERROR</code> on success
     */
    public abstract int doInit(boolean ignoreCancel) throws Throwable;

    /**
     * I believe this method is called after the initial states are computed
     * to do all the rest of the model checking.  LL 9 April 2012
     * <p>
     * Create the partial state space for given starting state up
     * to the given depth or the number of states.
     */
    public final int runTLC(final int depth) throws Exception {
        if (depth < 2) {
            return EC.NO_ERROR;
        }

        workers = startWorkers(this, depth);

        // Check progress periodically:
        // Comment added by LL on 9 April 2012.  The coverage is printed
        // every `count' times that the progress is printed.
        int count = TLCGlobals.coverageInterval / TLCGlobals.progressInterval;

        // I added the `if (!this.done)' to the following statement.
        // I have no idea what this wait is for, but apparently
        // because of changes made by Simon, it caused TLC to wait for
        // 30 seconds before exiting if it found an error right away.
        // It seems that the notify that's supposed to wake up the thread
        // in this case is being executed too soon. It also seems that
        // the thread doing the notify also sets this.done to true.
        // Thus, this fix should work. It would be nice to better understand
        // what's going on to be sure that this really does the trick.
        // LL 11 October 2009
        synchronized (this) {
            if (!this.done) {

                this.wait(3000);
            }
        }

        // Comments, written 9 April 2012 by LL.
        // It looks like the following while loop is responsible for checkpointing,
        // printing the coverage information, and printing the progress report,
        // as well as doing the periodic liveness checking.
        //
        // The doPeriodicWork() method performs the checkpointing as well as
        // liveness checking on the current state graph.

        // SZ Feb 23, 2009: exit if canceled
        // added condition to run in the cycle
        // while (true) {
        int result;
        while (!Thread.currentThread().isInterrupted()) {
            result = this.doPeriodicWork();
            if (result != EC.NO_ERROR) {
                return result;
            }
            synchronized (this) {
                if (!this.done) {
                    runTLCContinueDoing(count, depth);
                    // Changes made to runTLCContinueDoing require
                    // that the caller change count. LL 9 Oct 2009
                    if (count == 0) {
                        count = TLCGlobals.coverageInterval / TLCGlobals.progressInterval;
                    } else {
                        count--;
                    }
                }
                if (this.done)
                    break;
            }
        }

        // Wait for all the workers to terminate:
        for (final IWorker worker : workers) {
            worker.join();
        }
        if (!this.keepCallStack) {
            // A worker explicitly set an errorCode (without interrupting
            // state-space exploration) and doesn't request to keep the call-stack.
            // (If a call-stack is requested, this has to return NO_ERROR to not
            // intercept the outer logic)
            return this.errorCode != EC.NO_ERROR ? this.errorCode : EC.NO_ERROR;
        }
        return EC.NO_ERROR;
    }

    public final void setAllValues(final int idx, final IValue val) {
        for (final IWorker worker : this.workers) {
            worker.setLocalValue(idx, val);
        }
    }

    public final List<IValue> getAllValue(final int idx) {
        return Arrays.stream(workers).map(w -> w.getLocalValue(idx)).toList();
    }

    public final IValue getValue(final int i, final int idx) {
        return workers[i].getLocalValue(idx);
    }

    public final Value getAllValues() {
        final IValue[] localValues = ((IdThread) workers[0]).getLocalValues();

        final Map<Value, Value> m = new HashMap<>(localValues.length);

        for (int i = 0; i < localValues.length; i++) {
            final IValue iValue = localValues[i];
            if (iValue != null) {
                final Value[] vals = new Value[workers.length];
                for (int j = 0; j < vals.length; j++) {
                    vals[j] = (Value) workers[j].getLocalValue(i);
                }
                m.put(IntValue.gen(i), new TupleValue(vals));
            }
        }
        return new FcnRcdValue(m);
    }

    /**
     * Debugging support
     */
    protected void report(final String message) {
        DebugPrinter.print(message);
    }

    /**
     * The method for worker initialization and start
     *
     * @param checker    the checker instance
     * @param checkIndex the check level (depth or level)
     * @return the array of initialized worker threads
     */
    protected abstract IWorker[] startWorkers(AbstractChecker checker, int checkIndex);

    /**
     * Usually
     * Check liveness: check liveness properties on the partial state graph.
     * Checkpoint: checkpoint three data structures: the state set, the
     * state queue, and the state trace.
     *
     * @return an error code, or <code>EC.NO_ERROR</code> on success
     */
    public abstract int doPeriodicWork() throws Exception;

    /**
     * Method called from the main worker loop
     */
    protected abstract void runTLCContinueDoing(int count, int depth) throws Exception;

    /**
     * Main method of the model checker
     *
     * @return an error code, or <code>EC.NO_ERROR</code> on success
     */
    final public int modelCheck() throws Exception {
        final int result = modelCheckImpl();
        return (result != EC.NO_ERROR) ? result : errorCode;
    }

    protected abstract int modelCheckImpl() throws Exception;

    public int getProgress() {
        return -1;
    }

    public void suspend() {
        throw new UnsupportedOperationException("suspend not implemented");
    }

    public void resume() {
        throw new UnsupportedOperationException("resume not implemented");
    }

    public TLCStateInfo[] getTraceInfo(final TLCState s) throws IOException {
        throw new UnsupportedOperationException("getTraceInfo(TLCState) not implemented for this AbstractChecker");
    }

    public TLCStateInfo[] getTraceInfo(final TLCState from, final TLCState s) throws IOException {
        throw new UnsupportedOperationException("getTraceInfo(TLCState, TLCState) not implemented for this AbstractChecker");
    }

    protected boolean isTimeBound() {
        return Long.getLong(TLC.class.getName() + ".stopAfter", -1L) != -1;
    }

    public long getStateQueueSize() {
        return -1;
    }

    public long getDistinctStatesGenerated() {
        return -1;
    }

    public long getStatesGenerated() {
        return -1;
    }

    public final Value getStatistics() {
        final UniqueString[] n = new UniqueString[5];
        final Value[] v = new Value[n.length];

        n[0] = TLCGetSet.QUEUE;
        v[0] = TLCGetSet.narrowToIntValue(getStateQueueSize());

        n[1] = TLCGetSet.DISTINCT;
        v[1] = TLCGetSet.narrowToIntValue(getDistinctStatesGenerated());

        n[2] = TLCGetSet.GENERATED;
        v[2] = TLCGetSet.narrowToIntValue(getStatesGenerated());

        n[3] = TLCGetSet.DIAMETER;
        v[3] = TLCGetSet.narrowToIntValue(getProgress());

        n[4] = TLCGetSet.DURATION;
        v[4] = TLCGetSet.narrowToIntValue((System.currentTimeMillis() - startTime) / 1000L);

        return new RecordValue(n, v, false);
    }

    public final Value getConfig() {
        return config;
    }

    private Value createConfig() {
        final UniqueString[] n = new UniqueString[6];
        final Value[] v = new Value[n.length];
        n[0] = TLCGetSet.MODE;
        v[0] = new StringValue("bfs");

        n[1] = TLCGetSet.DEADLOCK;
        v[1] = checkDeadlock ? BoolValue.ValTrue : BoolValue.ValFalse;

        n[2] = TLCGetSet.WORKER;
        v[2] = IntValue.gen(TLCGlobals.getNumWorkers());

        n[3] = TLCGetSet.SEED;
        v[3] = new StringValue(Long.toString(RandomEnumerableValues.getSeed()));

        n[4] = TLCGetSet.FINGERPRINT;
        v[4] = new StringValue(Long.toString(FP64.getIrredPoly()));

        n[5] = TLCGetSet.INSTALL;
        v[5] = new StringValue(TLCGlobals.getInstallLocation());

        return new RecordValue(n, v, false);
    }

    public final boolean isRecovery() {
        return this.fromChkpt != null;
    }
}
