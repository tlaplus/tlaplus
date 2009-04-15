package tlc2.tool;

import java.io.File;
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.Date;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.util.IdThread;
import tlc2.util.ObjLongTable;
import tlc2.util.StateWriter;
import util.Assert;
import util.FileUtil;
import util.FilenameToStream;
import util.ToolIO;

/**
 * The abstract checker
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class AbstractChecker implements Cancelable
{
// SZ Mar 9, 2009: static modifier removed
    protected long nextLiveCheck;
    protected long numOfGenStates;
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
    protected long lastChkpt;
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

        // REFACTOR: file utilites
        this.metadir = makeMetaDir(specDir, fromChkpt);

        this.nextLiveCheck = 1000;
        this.numOfGenStates = 0;
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
        this.lastChkpt = System.currentTimeMillis();

        this.impliedInits = this.tool.getImpliedInits(); // implied-inits to be checked
        this.invariants = this.tool.getInvariants(); // invariants to be checked
        this.impliedActions = this.tool.getImpliedActions(); // implied-actions to be checked
        this.actions = this.tool.getActions(); // the sub-actions

    }

    public final void setDone()
    {
        this.done = true;
    }

    protected final synchronized void incNumOfGenStates(int n)
    {
        this.numOfGenStates += n;
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

    protected void reportCoverage(IWorker[] workers)
    {
          if (TLCGlobals.coverageInterval >= 0) {
              ToolIO.out.println("The coverage stats:");
              // First collecting all counts from all workers:
              ObjLongTable counts = this.tool.getPrimedLocs();
              for (int i = 0; i < workers.length; i++) {
                  ObjLongTable counts1 = workers[i].getCounts();
                  ObjLongTable.Enumerator keys = counts1.keys();
                  Object key;
                  while ((key = keys.nextElement()) != null) {
                      String loc = ((SemanticNode)key).getLocation().toString();
                      counts.add(loc, counts1.get(key));
                  }
              }
              // Reporting:
              Object[] skeys = counts.sortStringKeys();
              for (int i = 0; i < skeys.length; i++) {
                  long val = counts.get(skeys[i]);
                  ToolIO.out.println("  " + skeys[i] + ": " + val);
              }
          }
      }

    /**
     * The MetaDir is fromChkpt if it is not null. Otherwise, create a
     * new one based on the current time.
     * @param specDir the specification directory
     * @param fromChkpt, path of the checkpoints if recovering, or <code>null</code>
     * 
     * REFACTOR: move to FileUtils
     */
    public static String makeMetaDir(String specDir, String fromChkpt)
    {
        if (fromChkpt != null)
        {
            return fromChkpt;
        }
        String metadir = TLCGlobals.metaDir;
        if (metadir == null)
        {
            // If not given, use the directory specDir/metaRoot:
            metadir = specDir + TLCGlobals.metaRoot + FileUtil.separator;
        }

        SimpleDateFormat sdf = new SimpleDateFormat("yy-MM-dd-HH-mm-ss");
        metadir += sdf.format(new Date());
        File filedir = new File(metadir);
        if (filedir.exists())
        {
            Assert.fail("Error: TLC writes its files to a directory whose name is generated"
                    + " from the current time.\nThis directory should be " + metadir
                    + ", but that directory already exists.\n"
                    + "Trying to run TLC again will probably fix this problem.\n");
        } else
        {
            Assert.check(filedir.mkdirs(), "Error: TLC could not make a directory for the disk files"
                    + " it needs to write.\n");
        }
        return metadir;
    }

    /**
     * Initialize the model checker
     * @return
     * @throws Throwable
     */
    public abstract boolean doInit(boolean ignoreCancel) throws Throwable;
    
    /**
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
          IdThread[] workers = createAndStartWorkers(this, depth);
    
          // Check progress periodically:
          int count = TLCGlobals.coverageInterval/TLCGlobals.progressInterval;
          
          // work to be done prior loop entry
          runTLCPreLoop();
          
          synchronized(this) 
          {
              // sleep 30 seconds
              this.wait(30000); 
          }
          
          // SZ Feb 23, 2009: exit if canceled
          // added condition to run in the cycle
          // while (true) {
          while (!this.cancellationFlag) {
              long now = System.currentTimeMillis();
              if (now - this.lastChkpt >= TLCGlobals.chkptDuration) {
                  if (!this.doPeriodicWork()) 
                  { 
                      return false; 
                  }
                  this.lastChkpt = now;
              }
              synchronized(this) {
                  if (!this.done) {
                      runTLCContinueDoing(count, depth);
                  }
                  if (this.done) break;
              }
          }
    
          // Wait for all the workers to terminate:
          for (int i = 0; i < workers.length; i++) {
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
    protected abstract IdThread[] createAndStartWorkers(AbstractChecker checker, int checkIndex);
    
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
