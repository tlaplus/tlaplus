package tlc2.tool;

import java.io.IOException;
import java.util.concurrent.atomic.AtomicLong;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.util.IdThread;
import tlc2.util.ObjLongTable;
import tlc2.util.StateWriter;
import util.FileUtil;
import util.FilenameToStream;

/**
 * The abstract checker
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class AbstractChecker implements Cancelable
{
    // SZ Mar 9, 2009: static modifier removed
    protected long nextLiveCheck;
    protected AtomicLong numOfGenStates;
    protected TLCState predErrState;
    protected TLCState errState;
    protected boolean done;
    protected boolean keepCallStack;
    protected boolean checkDeadlock;
    protected boolean checkLiveness;
    protected String fromChkpt;
    public String metadir;
    public Tool tool;
    public Action[] invariants;
    public Action[] impliedActions;
    public Action[] impliedInits;
    public Action[] actions;
    protected StateWriter allStateWriter;
    protected boolean cancellationFlag;

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
    public AbstractChecker(String specFile, String configFile, String dumpFile, boolean deadlock, String fromChkpt,
            boolean preprocess, FilenameToStream resolver, SpecObj spec) throws EvalException, IOException
    {
        this.cancellationFlag = false;

        this.checkDeadlock = deadlock;

        int lastSep = specFile.lastIndexOf(FileUtil.separatorChar);
        String specDir = (lastSep == -1) ? "" : specFile.substring(0, lastSep + 1);
        specFile = specFile.substring(lastSep + 1);

        this.tool = new Tool(specDir, specFile, configFile, resolver);

        this.tool.init(preprocess, spec);
        this.checkLiveness = !this.tool.livenessIsTrue();

        // moved to file utilities
        this.metadir = FileUtil.makeMetaDir(specDir, fromChkpt);
        
        // The number of states generated before the first liveness check is
        // performed.  This value of 1000 sounds low, but since the value is
        // doubled after each check up to a maximum of 640K (a number embedded
        // in several places in the code), it probably doesn't much matter.
        this.nextLiveCheck = 1000;
        this.numOfGenStates = new AtomicLong(0);
        this.errState = null;
        this.predErrState = null;
        this.done = false;
        this.keepCallStack = false;

        this.fromChkpt = fromChkpt;

        // Initialize dumpFile:
        if (dumpFile != null)
        {
            this.allStateWriter = new StateWriter(dumpFile);
        }

        this.impliedInits = this.tool.getImpliedInits(); // implied-inits to be checked
        this.invariants = this.tool.getInvariants(); // invariants to be checked
        this.impliedActions = this.tool.getImpliedActions(); // implied-actions to be checked
        this.actions = this.tool.getActions(); // the sub-actions

    }

    public final void setDone()
    {
        this.done = true;
    }

    protected final void incNumOfGenStates(int n)
    {
        this.numOfGenStates.getAndAdd(n);
    }

    /**
     * Set the error state. 
     * <strong>Note:</note> this method must be protected by lock 
     */
    public boolean setErrState(TLCState curState, TLCState succState, boolean keep)
    {
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
        if (TLCGlobals.coverageInterval >= 0)
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

        // Start all the workers:
        IdThread[] workers = startWorkers(this, depth);

        // Check progress periodically:
        // Comment added by LL on 9 April 2012.  The coverage is printed
        // every `count' times that the progress is printed.
        int count = TLCGlobals.coverageInterval / TLCGlobals.progressInterval;

        // work to be done prior loop entry
        runTLCPreLoop();

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
            if (TLCGlobals.doCheckPoint())
            {
                if (!this.doPeriodicWork())
                {
                    return false;
                }
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

    /**
     * The method for worker initialization and start
     * @param checker the checker instance
     * @param checkIndex the check level (depth or level)
     * @return the array of initialized worker threads
     */
    protected abstract IdThread[] startWorkers(AbstractChecker checker, int checkIndex);

    /**
     * Hook to run some work before entering the worker loop
     */
    protected void runTLCPreLoop()
    {
    }

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
