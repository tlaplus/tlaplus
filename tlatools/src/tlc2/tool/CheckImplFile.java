// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:54 PST by lamport  
//      modified on Thu Jun 21 14:39:42 PDT 2001 by yuanyu   

package tlc2.tool;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintWriter;

import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.util.FP64;
import util.Assert;
import util.FileUtil;
import util.ToolIO;
import util.UniqueString;

/**
 * CheckImplFile is a subclass of CheckImpl. It uses files to
 * communicate with simulator.  Traces are stored in files.
 **/
public class CheckImplFile extends CheckImpl
{

    private static int WaitForTrace = 10000;

    /**
     * @param fpMemSize : Parameter added 6 Apr 2010 by Yuan Yu because it was added
     * to ModelChecker constructor.
     * 
     */
    public CheckImplFile(String specFile, String configFile, boolean deadlock, int depth, String fromChkpt,
            String traceFile, final FPSetConfiguration fpSetConfig) throws IOException
    {
        super(specFile, configFile, deadlock, depth, fromChkpt, fpSetConfig);
        this.traceFile = traceFile;
        this.states = null;
        this.sidx = 0;
        this.ticnt = 1;
        this.tocnt = 1;
    }

    private TLCState[] states;
    private int sidx;
    private String traceFile;
    private int ticnt;
    private int tocnt;

    /**
     * This method gets a new state from the external world via files.
     * It returns null if there is nothing available.
     */
    public final TLCState getState()
    {
        if (this.sidx < this.states.length)
        {
            return this.states[sidx++];
        }
        return null;
    }

    /* This method exports a trace by writing it into a file.  */
    public final void exportTrace(TLCStateInfo[] trace) throws IOException
    {
        String fname = this.traceFile + "_out_" + this.tocnt;
        FileOutputStream fos = new FileOutputStream(fname);
        PrintWriter pw = new PrintWriter(fos);
        for (int i = 0; i < trace.length; i++)
        {
            pw.println("STATE_" + (i + 1));
            pw.println(trace[i].state + "\n");
        }
        pw.close();
        this.tocnt++;
    }

    /* This method reads in a trace from a file. */
    public final boolean getTrace()
    {
        String rfname = this.traceFile + this.ticnt;
        File tfile = new File(rfname);
        ToolIO.out.println("Trying to work on trace " + tfile + " ...");
        if (!tfile.exists())
            return false;

        // Parse the trace file:
        // REFACTOR: Call SANY.frontendparse
        SpecObj spec = new SpecObj(rfname, null);
        try
        {
            SANY.frontEndInitialize(spec, ToolIO.out);
            SANY.frontEndParse(spec, ToolIO.out);
            SANY.frontEndSemanticAnalysis(spec, ToolIO.out, true);
        } catch (Throwable e)
        {
            String msg = (e.getMessage()==null)?e.toString():e.getMessage();
            Assert.fail(EC.CHECK_COULD_NOT_READ_TRACE, msg);
        }
        if (!spec.initErrors.isSuccess() || !spec.parseErrors.isSuccess() || !spec.semanticErrors.isSuccess())
        {
            Assert.fail(EC.TLC_PARSING_FAILED);
        }

        // Set the rootModule:
        ExternalModuleTable mt = spec.getExternalModuleTable();
        // SZ 11.04.2009: Changed access method
        ModuleNode module = mt.getModuleNode(UniqueString.uniqueStringOf(rfname));

        // Put the sequence of states in the trace into this.states:
        OpDefNode[] opDefs = module.getOpDefs();
        int len = opDefs.length;
        this.states = new TLCState[len];
        for (int i = 0; i < len; i++)
        {
            TLCState state = this.tool.makeState(opDefs[i].getBody());
            this.states[i] = state;
        }
        this.sidx = 0;
        this.ticnt++;
        return true;
    }

    /**
     * CheckImplFile and the simulation engine communicate via files:
     *
     * 1. The simulation engine stores in files the abstract view of
     * the states it generates during the simulation run. The abstract
     * view of simulation state is computed by a refinement function.
     * CheckImplFile checks the abstract states in the files.
     *
     * 2. CheckImplFile maintains coverage information while doing the
     * checking.  It continuously generates traces to uncovered states,
     * and store the traces in files.  The simulation engine uses the
     * traces in the files to guide the simulation into the parts of
     * the state space that simulation fails to reach up to that point.
     *
     * Usage: java tlc2.tool.CheckImplFile [options] spec[.tla]
     *
     * Below is a list of the command line options:
     *  o -config file: provide the config file.
     *    Defaults to spec.cfg if not provided
     *  o -deadlock: do not check for deadlock.
     *    Defaults to checking deadlock if not specified
     *  o -recover path: recover from checkpoint in path
     *    Defaults to scratch run if not specified
     *  o -workers num: the number of TLC worker threads
     *    Defaults to 1
     *  o -depth num: the depth of the initial (partial) state space
     *    Defaults to 20
     *  o -trace filename: the prefix of the trace file name.   
     *  o -coverage seconds: collect coverage information on the spec,
     *                       print out the information every seconds
     *    Defaults to no coverage if not specified
     **/
    public static void main(String[] args) {
    ToolIO.out.println("TLC CheckImpl" + TLCGlobals.versionOfTLC);

    String mainFile = null;
    String configFile = null;
    String traceFile = null;
    boolean deadlock = true;
    int depth = 20;
    String fromChkpt = null;

    int index = 0;
    while (index < args.length) {
        if (args[index].equals("-config")) {
            index++;
            if (index < args.length) {
                configFile = args[index++];
                int len = configFile.length();
                if (configFile.startsWith(".cfg", len-4)) {
                    configFile = configFile.substring(0, len-4);
                }
            }
            else {
                printErrorMsg(MP.getMessage(EC.CHECK_PARAM_EXPECT_CONFIG_FILENAME));
                return;
            }
        }
        else if (args[index].equals("-deadlock")) {
            index++;
            deadlock = false;
        }	
        else if (args[index].equals("-recover")) {
            index++;
            if (index < args.length) {
                fromChkpt = args[index++] + FileUtil.separator;
            }
            else {
                printErrorMsg(MP.getMessage(EC.CHECK_PARAM_NEED_TO_SPECIFY_CONFIG_DIR));
                return;
            }
        }
        else if (args[index].equals("-workers")) {
            index++;
            if (index < args.length) {
                try 
                {
                    TLCGlobals.setNumWorkers(Integer.parseInt(args[index]));
                    index++;
                } catch (NumberFormatException e) 
                {
                    printErrorMsg(MP.getMessage(EC.CHECK_PARAM_WORKER_NUMBER_REQUIRED, args[index]));
                    return;
                }
                if (TLCGlobals.getNumWorkers() < 1) 
                {
                    printErrorMsg(MP.getMessage(EC.CHECK_PARAM_WORKER_NUMBER_TOO_SMALL));
                    return;
                }
            } else 
            {
                printErrorMsg(MP.getMessage(EC.CHECK_PARAM_WORKER_NUMBER_REQUIRED2));
                return;
            }
        }
        else if (args[index].equals("-depth")) {
            index++;
            if (index < args.length) {
                try {
                    depth = Integer.parseInt(args[index]);
                    index++;
                }
                catch (NumberFormatException e) 
                {
                    printErrorMsg(MP.getMessage(EC.CHECK_PARAM_DEPTH_REQUIRED, args[index]));
                    return;
                }
            }
            else {
                printErrorMsg(MP.getMessage(EC.CHECK_PARAM_DEPTH_REQUIRED2));
                return;
            }
        }
        else if (args[index].equals("-trace")) {
            index++;
            if (index < args.length) {
                traceFile = args[index++];
            }
            else {
                printErrorMsg(MP.getMessage(EC.CHECK_PARAM_TRACE_REQUIRED));
                return;
            }
        }
        else if (args[index].equals("-coverage")) {
            index++;
            if (index < args.length) {
                try {
                    TLCGlobals.coverageInterval = Integer.parseInt(args[index]) * 1000 * 60;
                    if (TLCGlobals.coverageInterval < 0) {
                        printErrorMsg(MP.getMessage(EC.CHECK_PARAM_COVREAGE_TOO_SMALL));
                        return;
                    }
                    index++;
                }
                catch (NumberFormatException e) {
                    printErrorMsg(MP.getError(EC.CHECK_PARAM_COVREAGE_REQUIRED, args[index]));
                    return;
                }
            }
            else {
                printErrorMsg(MP.getError(EC.CHECK_PARAM_COVREAGE_REQUIRED));
                return;
            }
        }
        else {
            if (args[index].charAt(0) == '-') {
                printErrorMsg(MP.getError(EC.CHECK_PARAM_UNRECOGNIZED, args[index]));
                return;
            }
            if (mainFile != null) {
                printErrorMsg(MP.getError(EC.CHECK_PARAM_UNRECOGNIZED, new String[]{mainFile, args[index] }));
                return;
            }
            mainFile = args[index++];
            int len = mainFile.length();
            if (mainFile.startsWith(".tla", len-4)) {
                mainFile = mainFile.substring(0, len-4);
            }
        }
    }

    if (mainFile == null) {
      printErrorMsg(MP.getMessage(EC.CHECK_PARAM_MISSING_TLA_MODULE));
      return;
    }

    if (configFile == null) configFile = mainFile;
    if (traceFile == null) traceFile = mainFile + "_trace";

    try {
      // Initialize:
      if (fromChkpt != null) {
        // We must recover the intern var table as early as possible
        UniqueString.internTbl.recover(fromChkpt);
      }
      FP64.Init(0);
      
      // Start the checker:
      CheckImplFile checker = new CheckImplFile(mainFile, configFile, deadlock,
						depth, fromChkpt, traceFile, new FPSetConfiguration());
      checker.init();
      while (true) {
	// Get a trace and check it.
	checker.export();
	boolean ok = checker.getTrace();
	if (ok) {
	  checker.checkTrace();
	}
	else {
	  synchronized(checker) { checker.wait(WaitForTrace); }
	}
      }
    }
    catch (Throwable e) 
    {
      MP.printError(EC.CHECK_FAILED_TO_CHECK, e);
    }
    System.exit(0);    
  }

    private static void printErrorMsg(String msg)
    {
        ToolIO.out.println(msg);
        MP.printError(EC.CHECK_PARAM_USAGE);
    }

}
