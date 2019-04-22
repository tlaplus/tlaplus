package tlc2.tool;

import java.io.IOException;
import java.math.BigDecimal;
import java.math.MathContext;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.coverage.CostModelCreator;
import tlc2.tool.liveness.AddAndCheckLiveCheck;
import tlc2.tool.liveness.ILiveCheck;
import tlc2.tool.liveness.LiveCheck;
import tlc2.tool.liveness.Liveness;
import tlc2.tool.liveness.NoOpLiveCheck;
import tlc2.util.IStateWriter;
import tlc2.util.IdThread;
import tlc2.util.statistics.ConcurrentBucketStatistics;
import tlc2.util.statistics.DummyBucketStatistics;
import tlc2.util.statistics.IBucketStatistics;
import tlc2.value.IValue;
import util.DebugPrinter;

/**
 * The abstract checker
 * @author Simon Zambrovski
 */
public abstract class AbstractChecker
{
	/**
	 * True when unit tests explicitly request to use
	 * {@link AddAndCheckLiveCheck} to run liveness checking after each
	 * insertion into the behavior graph. This should only be true if you
	 * exactly know what you are doing. If you don't and this is true, make sure
	 * it's false.
	 */
	public static boolean LIVENESS_TESTING_IMPLEMENTATION = Boolean.getBoolean(ILiveCheck.class.getName() + ".testing");
	
	protected static final boolean LIVENESS_STATS = Boolean.getBoolean(Liveness.class.getPackage().getName() + ".statistics");
	
    protected TLCState predErrState;
    protected TLCState errState;
    protected boolean done;
    protected boolean keepCallStack;
    protected final boolean checkDeadlock;
    protected final boolean checkLiveness;
    protected final String fromChkpt;
    public final String metadir;
    public final ITool tool;
    protected final IStateWriter allStateWriter;
    protected IWorker[] workers;
	protected final ILiveCheck liveCheck;

    /**
     * Constructor of the abstract model checker
     * @param specFile
     * @param configFile
     * @param dumpFile
     * @param deadlock
     * @param fromChkpt
     * @param preprocess
     * @param resolver
     * @param spec - pre-built specification object (e.G. from calling SANY from the tool previously)
     */
	public AbstractChecker(ITool tool, String metadir, final IStateWriter stateWriter,
			boolean deadlock, String fromChkpt) throws EvalException, IOException {
        this.tool = tool;
		
		this.checkDeadlock = deadlock;
        this.checkLiveness = !this.tool.livenessIsTrue();

        // moved to file utilities
        this.metadir = metadir;
        
        this.errState = null;
        this.predErrState = null;
        this.done = false;
        this.keepCallStack = false;

        this.fromChkpt = fromChkpt;
        
        this.allStateWriter = stateWriter;

        if (TLCGlobals.isCoverageEnabled()) {
        	CostModelCreator.create(this.tool);
        }
        
        if (this.checkLiveness) {
        	if (tool.hasSymmetry()) {
        		// raise warning...
				MP.printWarning(EC.TLC_FEATURE_UNSUPPORTED_LIVENESS_SYMMETRY);
        	}
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
    }

    public final void setDone()
    {
        this.done = true;
    }

    /**
     * Set the error state. 
     * <strong>Note:</note> this method must be protected by lock 
     */
    public boolean setErrState(TLCState curState, TLCState succState, boolean keep)
    {
       assert Thread.holdsLock(this) : "Caller thread has to hold monitor!";
       if (!TLCGlobals.continuation && this.done)
            return false;
        IdThread.resetCurrentState();
        this.predErrState = curState;
        this.errState = (succState == null) ? curState : succState;
        this.done = true;
        this.keepCallStack = keep;
        return true;
    }

    /**
     * Responsible for printing the coverage information
     * @param workers
     */
    protected void reportCoverage(IWorker[] workers)
    {
		// Without actions (empty spec) there won't be any statistics anyway.
		if (TLCGlobals.isCoverageEnabled() && this.tool.getActions().length > 0)
		{
            CostModelCreator.report(this.tool);
        }
    }
    
    public static final double calculateOptimisticProbability(final long numOfDistinctStates, final long numOfGenStates) {
        return numOfDistinctStates * ((numOfGenStates - numOfDistinctStates) / Math.pow(2, 64));
    }
    
	public static final void reportSuccess(final long numOfDistinctStates, final long numOfGenStates)
			throws IOException {
		final double optimisticProb = calculateOptimisticProbability(numOfDistinctStates, numOfGenStates);
		MP.printMessage(EC.TLC_SUCCESS, new String[] { "val = " + ProbabilityToString(optimisticProb, 2) });
	}
   
	public static final void reportSuccess(final long numOfDistinctStates, final long actualDistance,
			final long numOfGenStates) throws IOException {
		// Prevent div-by-zero when calculating collision probabilities when no states
		// are generated.
		if (numOfDistinctStates == numOfGenStates && numOfGenStates == 0) {
			// When the number of states is zero, printing a collision probability is
			// useless anyway. But the Toolbox will probably crash if omitted.
			MP.printMessage(EC.TLC_SUCCESS, new String[] { "val = 0.0", "val = 0.0" });
			return;
		}
		// shown as 'calculated' in Toolbox
		final String optimisticProbStr = "val = "
				+ ProbabilityToString(calculateOptimisticProbability(numOfDistinctStates, numOfGenStates), 2);

		// shown as 'observed' in Toolbox
		final BigDecimal actualProb = BigDecimal.valueOf(1d).divide(BigDecimal.valueOf(actualDistance),
				new MathContext(2));
		final String actualProbStr = "val = " + actualProb.toString();
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

    /**
     * Initialize the model checker
     * @return
     * @throws Throwable
     */
    public abstract boolean doInit(boolean ignoreCancel) throws Throwable;

    /**
     * I believe this method is called after the initial states are computed
     * to do all the rest of the model checking.  LL 9 April 2012
     * 
     * Create the partial state space for given starting state up
     * to the given depth or the number of states.
     */
    public final boolean runTLC(int depth) throws Exception
    {
        if (depth < 2)
        {
            return true;
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
        synchronized (this)
        {
            if (!this.done)
            {

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
        while (true)
        {
            if (!this.doPeriodicWork())
            {
                return false;
            }
            synchronized (this)
            {
                if (!this.done)
                {
                    runTLCContinueDoing(count, depth);
                    // Changes made to runTLCContinueDoing require
                    // that the caller change count. LL 9 Oct 2009
                    if (count == 0)
                    {
                        count = TLCGlobals.coverageInterval / TLCGlobals.progressInterval;
                    } else
                    {
                        count--;
                    }
                }
                if (this.done)
                    break;
            }
        }

        // Wait for all the workers to terminate:
        for (int i = 0; i < workers.length; i++)
        {
            workers[i].join();
        }
        return true;
    }
    
	public final void setAllValues(int idx, IValue val) {
		for (int i = 0; i < this.workers.length; i++) {
			workers[i].setLocalValue(idx, val);
		}
	}

	public final IValue getValue(int i, int idx) {
		return workers[i].getLocalValue(idx);
	}

    /**
     * Debugging support
     * @param message
     */
    protected void report(String message)
    {
        DebugPrinter.print(message);
    }

    /**
     * The method for worker initialization and start
     * @param checker the checker instance
     * @param checkIndex the check level (depth or level)
     * @return the array of initialized worker threads
     */
    protected abstract IWorker[] startWorkers(AbstractChecker checker, int checkIndex);

    /**
     * Usually
     * Check liveness: check liveness properties on the partial state graph.
     * Checkpoint: checkpoint three data structures: the state set, the
     *             state queue, and the state trace.
     * @return
     * @throws Exception
     */
    public abstract boolean doPeriodicWork() throws Exception;

    /**
     * Method called from the main worker loop
     * @param count
     * @param depth
     * @throws Exception
     */
    protected abstract void runTLCContinueDoing(int count, int depth) throws Exception;

    /**
     * Main method of the model checker
     * @throws Exception
     */
    public abstract void modelCheck() throws Exception;

	public int getProgress() {
		return -1;
	}
	
	public void stop() {
		// Noop
	}
	
	public void suspend() {
		// Noop
	}
	
	public void resume() {
		// Noop
	}

	public long getStateQueueSize() {
		return -1;
	}

	public long getDistinctStatesGenerated() {
		return -1;
	}
}
