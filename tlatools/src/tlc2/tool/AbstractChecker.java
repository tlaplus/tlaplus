package tlc2.tool;

import java.io.IOException;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.liveness.AddAndCheckLiveCheck;
import tlc2.tool.liveness.ILiveCheck;
import tlc2.tool.liveness.LiveCheck;
import tlc2.tool.liveness.Liveness;
import tlc2.tool.liveness.NoOpLiveCheck;
import tlc2.util.DotStateWriter;
import tlc2.util.IStateWriter;
import tlc2.util.NoopStateWriter;
import tlc2.util.ObjLongTable;
import tlc2.util.StateWriter;
import tlc2.util.statistics.ConcurrentBucketStatistics;
import tlc2.util.statistics.DummyBucketStatistics;
import tlc2.util.statistics.IBucketStatistics;
import tlc2.value.Value;
import util.DebugPrinter;
import util.FileUtil;
import util.FilenameToStream;

/**
 * The abstract checker
 * @author Simon Zambrovski
 */
public abstract class AbstractChecker implements Cancelable
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
    protected boolean checkDeadlock;
    protected boolean checkLiveness;
    protected String fromChkpt;
    public String metadir;
    public Tool tool;
    public final SpecObj specObj;
    public Action[] invariants;
    public Action[] impliedActions;
    public Action[] impliedInits;
    public Action[] actions;
    protected final IStateWriter allStateWriter;
    protected boolean cancellationFlag;
    protected IWorker[] workers;
	protected final ILiveCheck liveCheck;

	protected final ThreadLocal<Integer> threadLocal = new ThreadLocal<Integer>() {
		protected Integer initialValue() {
			return 1;
		}
	};

	protected static final int INITIAL_CAPACITY = 16;

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
    public AbstractChecker(String specFile, String configFile, String dumpFile, final boolean asDot, final boolean colorize, final boolean actionLabels, boolean deadlock, String fromChkpt,
            boolean preprocess, FilenameToStream resolver, SpecObj spec) throws EvalException, IOException
    {
        this.cancellationFlag = false;

        this.checkDeadlock = deadlock;

        int lastSep = specFile.lastIndexOf(FileUtil.separatorChar);
        String specDir = (lastSep == -1) ? "" : specFile.substring(0, lastSep + 1);
        specFile = specFile.substring(lastSep + 1);

        this.tool = new Tool(specDir, specFile, configFile, resolver);

        this.specObj = this.tool.init(preprocess, spec);
        this.checkLiveness = !this.tool.livenessIsTrue();

        // moved to file utilities
        this.metadir = FileUtil.makeMetaDir(specDir, fromChkpt);
        
        this.errState = null;
        this.predErrState = null;
        this.done = false;
        this.keepCallStack = false;

        this.fromChkpt = fromChkpt;

        // Initialize dumpFile:
        if (dumpFile != null)
        {
        	if (dumpFile.startsWith("${metadir}")) {
				// prefix dumpfile with the known value of this.metadir. There
				// is no way to determine the actual value of this.metadir
				// before TLC startup and thus it's impossible to make the
				// dumpfile end up in the metadir if desired.
        		dumpFile = dumpFile.replace("${metadir}", this.metadir);
        	}
        	if (asDot) {
        		this.allStateWriter = new DotStateWriter(dumpFile, colorize, actionLabels);
        	} else {
        		this.allStateWriter = new StateWriter(dumpFile);
        	}
        } else {
        	 this.allStateWriter = new NoopStateWriter();
        }

        this.impliedInits = this.tool.getImpliedInits(); // implied-inits to be checked
        this.invariants = this.tool.getInvariants(); // invariants to be checked
        this.impliedActions = this.tool.getImpliedActions(); // implied-actions to be checked
        this.actions = this.tool.getActions(); // the sub-actions

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
				this.liveCheck = new AddAndCheckLiveCheck(this.tool, this.actions, this.metadir, stats);
			} else {
				this.liveCheck = new LiveCheck(this.tool, this.actions, this.metadir, stats, dumpFile);
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
		if (TLCGlobals.coverageInterval >= 0 && this.actions.length > 0)
		{
            MP.printMessage(EC.TLC_COVERAGE_START);
            // First collecting all counts from all workers:
            ObjLongTable counts = this.tool.getPrimedLocs();
            for (int i = 0; i < workers.length; i++)
            {
                ObjLongTable counts1 = workers[i].getCounts();
                ObjLongTable.Enumerator keys = counts1.keys();
                Object key;
                while ((key = keys.nextElement()) != null)
                {
                    String loc = ((SemanticNode) key).getLocation().toString();
                    counts.add(loc, counts1.get(key));
                }
            }
            // Reporting:
            Object[] skeys = counts.sortStringKeys();
            for (int i = 0; i < skeys.length; i++)
            {
                long val = counts.get(skeys[i]);
                MP.printMessage(EC.TLC_COVERAGE_VALUE, new String[] { skeys[i].toString(), String.valueOf(val) });
            }
            MP.printMessage(EC.TLC_COVERAGE_END);
        }
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
        // SZ Feb 23, 2009: exit if canceled
        if (this.cancellationFlag)
        {
            return false;
        }

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
        while (!this.cancellationFlag)
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

    public void setCancelFlag(boolean flag)
    {
        this.cancellationFlag = flag;
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
}
