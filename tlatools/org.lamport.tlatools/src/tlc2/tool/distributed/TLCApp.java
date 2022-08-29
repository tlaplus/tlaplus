// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:57 PST by lamport  
//      modified on Fri Jul 27 10:47:59 PDT 2001 by yuanyu   
package tlc2.tool.distributed;

import model.InJarFilenameToStream;
import model.ModelInJar;
import tlc2.TLCGlobals;
import tlc2.tool.*;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.impl.CallStackTool;
import tlc2.tool.impl.FastTool;
import tlc2.util.FP64;
import util.*;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.List;

public class TLCApp extends DistApp {

    public final Action[] invariants; // the invariants to be checked
    public final Action[] impliedInits; // the implied-inits to be checked
    public final Action[] impliedActions; // the implied-actions to be checked
    public final Action[] actions; // the subactions
    private final String config;
    private final boolean checkDeadlock; // check deadlock?
    private final boolean preprocess; // preprocess?
    /* Fields */
    public ITool tool;
    private String fromChkpt = null; // recover from this checkpoint
    private String metadir = null; // the directory pathname for metadata
    private FPSetConfiguration fpSetConfig;
    /* Constructors */
    public TLCApp(final String specFile, final String configFile, final boolean deadlock,
                  final String fromChkpt, final FPSetConfiguration fpSetConfig) {
        this(specFile, configFile, deadlock, null);

        this.fromChkpt = fromChkpt;
        this.metadir = FileUtil.makeMetaDir(this.tool.getSpecDir(), fromChkpt);
        this.fpSetConfig = fpSetConfig;
    }
    public TLCApp(final String specFile, final String configFile, final boolean deadlock,
                  final String fromChkpt, final FPSetConfiguration fpSetConfig, final FilenameToStream fts) {
        this(specFile, configFile, deadlock, fts);

        this.fromChkpt = fromChkpt;
        this.metadir = FileUtil.makeMetaDir(this.tool.getSpecDir(), fromChkpt);
        this.fpSetConfig = fpSetConfig;
    }
    // TODO too many constructors redefinitions, replace with this(..) calls
    public TLCApp(String specFile, final String configFile,
                  final Boolean deadlock, final FilenameToStream fts) {

        // get the spec dir from the spec file
        final int lastSep = specFile.lastIndexOf(File.separatorChar);
        final String specDir = (lastSep == -1) ? "" : specFile.substring(0,
                lastSep + 1);
        specFile = specFile.substring(lastSep + 1);

        this.config = configFile;


        this.checkDeadlock = deadlock;
        this.preprocess = true;
        this.tool = new FastTool(specDir, specFile, configFile, fts, new HashMap<>());

        this.impliedInits = this.tool.getImpliedInits();
        this.invariants = this.tool.getInvariants();
        this.impliedActions = this.tool.getImpliedActions();
        this.actions = this.tool.getActions();
    }

    @SuppressWarnings("deprecation")
    public static TLCApp create(final String[] args) throws IOException {
        String specFile = null;
        String configFile = null;
        boolean deadlock = true;
        int fpIndex = 0;
        String fromChkpt = null;

        final FPSetConfiguration fpSetConfig = new FPSetConfiguration();

        int index = 0;
        while (index < args.length) {
            switch (args[index]) {
                case "-config" -> {
                    index++;
                    if (index < args.length) {
                        configFile = args[index];
                        if (configFile.endsWith(TLAConstants.Files.CONFIG_EXTENSION)) {
                            configFile = configFile.substring(0,
                                    (configFile.length() - TLAConstants.Files.CONFIG_EXTENSION.length()));
                        }
                        index++;
                    } else {
                        printErrorMsg("Error: configuration file required.");
                        return null;
                    }
                }
                case "-tool" -> {
                    index++;
                    TLCGlobals.tool = true;
                }
                case "-deadlock" -> {
                    index++;
                    deadlock = false;
                }
                case "-recover" -> {
                    index++;
                    if (index < args.length) {
                        fromChkpt = args[index++] + FileUtil.separator;
                    } else {
                        printErrorMsg("Error: need to specify the metadata directory for recovery.");
                        return null;
                    }
                }
                case "-checkpoint" -> {
                    index++;
                    if (index < args.length) {
                        try {
                            TLCGlobals.chkptDuration = (long) Integer.parseInt(args[index]) * 1000 * 60;
                            if (TLCGlobals.chkptDuration < 0) {
                                printErrorMsg("Error: expect a nonnegative integer for -checkpoint option.");
                            }

                            index++;
                        } catch (final Exception e) {
                            printErrorMsg("Error: An integer for checkpoint interval is required. But encountered "
                                    + args[index]);
                        }
                    } else {
                        printErrorMsg("Error: checkpoint interval required.");
                    }
                }
                case "-coverage" -> {
                    index++;
                    if (index < args.length) {
                        try {
                            // Coverage reporting is broken is distributed TLC. Thus
                            // warn the user and continue ignoring the parameter.
                            // Consume its value though.
                            ToolIO.out.println(
                                    "Warning: coverage reporting not supported in distributed TLC, ignoring -coverage "
                                            + args[index] + " parameter.");
                            index++;
                        } catch (final Exception e) {
                            printErrorMsg("Error: An integer for coverage report interval required."
                                    + " But encountered " + args[index]);
                            return null;
                        }
                    } else {
                        printErrorMsg("Error: coverage report interval required.");
                        return null;
                    }
                }
                case "-terse" -> {
                    index++;
                    TLCGlobals.expand = false;
                }
                case "-nowarning" -> {
                    index++;
                    TLCGlobals.warn = false;
                }
                case "-maxSetSize" -> {
                    index++;
                    if (index < args.length) {
                        try {
                            final int bound = Integer.parseInt(args[index]);

                            // make sure it's in valid range
                            if (!TLCGlobals.isValidSetSize(bound)) {
                                final int maxValue = Integer.MAX_VALUE;
                                printErrorMsg("Error: Value in interval [0, " + maxValue + "] for maxSetSize required. But encountered " + args[index]);
                                return null;
                            }
                            TLCGlobals.setBound = bound;

                            index++;
                        } catch (final Exception e) {
                            printErrorMsg("Error: An integer for maxSetSize required. But encountered " + args[index]);
                            return null;
                        }
                    } else {
                        printErrorMsg("Error: maxSetSize required.");
                        return null;
                    }
                }
                case "-fp" -> {
                    index++;
                    if (index < args.length) {
                        try {
                            fpIndex = Integer.parseInt(args[index]);
                            if (fpIndex < 0 || fpIndex >= FP64.Polys.length) {
                                printErrorMsg("Error: The number for -fp must be between 0 and "
                                        + (FP64.Polys.length - 1) + " (inclusive).");
                                return null;
                            }
                            index++;
                        } catch (final Exception e) {
                            printErrorMsg("Error: A number for -fp is required. But encountered "
                                    + args[index]);
                            return null;
                        }
                    } else {
                        printErrorMsg("Error: expect an integer for -workers option.");
                        return null;
                    }
                }
                case "-fpbits" -> {
                    index++;
                    if (index < args.length) {
                        try {
                            final int fpBits = Integer.parseInt(args[index]);

                            // make sure it's in valid range
                            if (!FPSet.isValid(fpBits)) {
                                printErrorMsg("Error: Value in interval [0, 30] for fpbits required. But encountered " + args[index]);
                                return null;
                            }
                            fpSetConfig.setFpBits(fpBits);

                            index++;
                        } catch (final Exception e) {
                            printErrorMsg("Error: A number for -fpbits is required. But encountered "
                                    + args[index]);
                            return null;
                        }
                    } else {
                        printErrorMsg("Error: expect an integer for -workers option.");
                        return null;
                    }
                }
                case "-fpmem" -> {
                    index++;
                    if (index < args.length) {
                        try {
                            // -fpmem can be used in two ways:
                            // a) to set the relative memory to be used for fingerprints (being machine independent)
                            // b) to set the absolute memory to be used for fingerprints
                            //
                            // In order to set memory relatively, a value in the domain [0.0, 1.0] is interpreted as a fraction.
                            // A value in the [2, Double.MaxValue] domain allocates memory absolutely.
                            //
                            // Independently of relative or absolute mem allocation,
                            // a user cannot allocate more than JVM heap space
                            // available. Conversely there is the lower hard limit TLC#MinFpMemSize.
                            final double fpmem = Double.parseDouble(args[index]);
                            if (fpmem < 0) {
                                printErrorMsg("Error: An positive integer or a fraction for fpset memory size/percentage required. But encountered " + args[index]);
                                return null;
                            } else if (fpmem > 1) {
                                // For legacy reasons we allow users to set the
                                // absolute amount of memory. If this is the case,
                                // we know the user intends to allocate all 100% of
                                // the absolute memory to the fpset.
                                ToolIO.out
                                        .println("Using -fpmem with an abolute memory value has been deprecated. " +
                                                "Please allocate memory for the TLC process via the JVM mechanisms " +
                                                "and use -fpmem to set the fraction to be used for fingerprint storage.");
                                fpSetConfig.setMemory((long) fpmem);
                                fpSetConfig.setRatio(1.0);
                            } else {
                                fpSetConfig.setRatio(fpmem);
                            }
                            index++;
                        } catch (final Exception e) {
                            printErrorMsg("Error: A positive integer or a fraction for fpset memory size/percentage required. But encountered " + args[index]);
                            return null;
                        }
                    }
                }
                case "-metadir" -> {
                    index++;
                    if (index < args.length) {
                        TLCGlobals.metaDir = args[index++] + FileUtil.separator;
                    } else {
                        printErrorMsg("Error: need to specify the metadata directory.");
                        return null;
                    }
                }
                default -> {
                    if (args[index].charAt(0) == '-') {
                        printErrorMsg("Error: unrecognized option: " + args[index]);
                        return null;
                    }
                    if (specFile != null) {
                        printErrorMsg("Error: more than one input files: "
                                + specFile + " and " + args[index]);
                        return null;
                    }
                    specFile = args[index++];
                    if (specFile.endsWith(TLAConstants.Files.TLA_EXTENSION)) {
                        specFile = specFile.substring(0, (specFile.length() - TLAConstants.Files.TLA_EXTENSION.length()));
                    }
                }
            }
        }

        if (specFile == null) {
            // command line omitted name of spec file, take this as an
            // indicator to check the in-jar model/ folder for a spec.
            // If a spec is found, use it instead.
            if (ModelInJar.hasModel()) {
                ModelInJar.loadProperties(); // Reads result.mail.address and so on.
                TLCGlobals.tool = true; // always run in Tool mode (to parse output by Toolbox later)
                TLCGlobals.chkptDuration = 0; // never use checkpoints with distributed TLC (highly inefficient)
                FP64.Init(fpIndex);
                final FilenameToStream resolver = new InJarFilenameToStream(ModelInJar.PATH);
                return new TLCApp(TLAConstants.Files.MODEL_CHECK_FILE_BASENAME, TLAConstants.Files.MODEL_CHECK_FILE_BASENAME,
                        deadlock, fromChkpt, fpSetConfig, resolver);
            }

            printErrorMsg("Error: Missing input TLA+ module.");
            return null;
        }
        if (configFile == null)
            configFile = specFile;

        if (fromChkpt != null) {
            // We must recover the intern table as early as possible
            UniqueString.internTbl.recover(fromChkpt);
        }
        FP64.Init(fpIndex);

        return new TLCApp(specFile, configFile, deadlock, fromChkpt, fpSetConfig);
    }

    private static void printErrorMsg(final String msg) {
        ToolIO.out.println(msg);
        ToolIO.out
                .println("Usage: java tlc2.tool.TLCServer [-option] inputfile");
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#getCheckDeadlock()
     */
    @Override
    public final Boolean getCheckDeadlock() {
        return this.checkDeadlock;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#getPreprocess()
     */
    @Override
    public final Boolean getPreprocess() {
        return this.preprocess;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#getFileName()
     */
    @Override
    public final String getFileName() {
        return this.tool.getRootFile();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#getSpecDir()
     */
    @Override
    public String getSpecDir() {
        return this.tool.getSpecDir();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#getConfigName()
     */
    @Override
    public String getConfigName() {
        return this.config;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#getMetadir()
     */
    @Override
    public final String getMetadir() {
        return this.metadir;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#canRecover()
     */
    @Override
    public final boolean canRecover() {
        return this.fromChkpt != null;
    }

    public List<File> getModuleFiles() {
        return this.tool.getModuleFiles(new InJarFilenameToStream(ModelInJar.PATH));
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#getInitStates(tlc2.tool.IStateFunctor)
     */
    @Override
    public final void getInitStates(final IStateFunctor functor) {
        this.tool.getInitStates(functor);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#getNextStates(tlc2.tool.TLCState)
     */
    @Override
    public final TLCState[] getNextStates(final TLCState curState)
            throws WorkerException {
        StateVec nextStates = new StateVec(10);
        for (final Action curAction : this.actions) {
            final StateVec nstates = this.tool.getNextStates(curAction,
                    curState);

            nextStates.addAll(nstates);
        }
        final int len = nextStates.size();
        if (len == 0 && this.checkDeadlock) {
            throw new WorkerException("Error: deadlock reached.", curState,
                    null, false);
        }
        final TLCState[] res = new TLCState[nextStates.size()];
        for (int i = 0; i < nextStates.size(); i++) {
            final TLCState succState = nextStates.get(i);
            if (!this.tool.isGoodState(succState)) {
                final String msg = "Error: Successor state is not completely specified by"
                        + " the next-state action.";
                throw new WorkerException(msg, curState, succState, false);
            }
            // isInModel, isInAction and invariant and implied action checks are
            // carried out later in TLCWorker#getNextStates(..) and below in
            // checkState(State, State) when it is know that the states are new
            // (after the call to the fingerprint set).
            res[i] = succState;
        }
        return res;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#checkState(tlc2.tool.TLCState, tlc2.tool.TLCState)
     */
    @Override
    public final void checkState(final TLCState s1, final TLCState s2)
            throws WorkerException {
        final TLCState ts2 = s2;
        for (int i = 0; i < this.invariants.length; i++) {
            if (!tool.isValid(this.invariants[i], ts2)) {
                // We get here because of invariant violation:
                final String msg = "Error: Invariant " + this.tool.getInvNames()[i]
                        + " is violated.";
                throw new WorkerException(msg, s1, s2, false);
            }
        }
        if (s1 == null) {
            for (int i = 0; i < this.impliedInits.length; i++) {
                if (!this.tool.isValid(this.impliedInits[i], ts2)) {
                    // We get here because of implied-inits violation:
                    final String msg = "Error: Implied-init "
                            + this.tool.getImpliedInitNames()[i]
                            + " is violated.";
                    throw new WorkerException(msg, s1, s2, false);
                }
            }
        } else {
            final TLCState ts1 = s1;
            for (int i = 0; i < this.impliedActions.length; i++) {
                if (!tool.isValid(this.impliedActions[i], ts1, ts2)) {
                    // We get here because of implied-action violation:
                    final String msg = "Error: Implied-action "
                            + this.tool.getImpliedActNames()[i]
                            + " is violated.";
                    throw new WorkerException(msg, s1, s2, false);
                }
            }
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#isInModel(tlc2.tool.TLCState)
     */
    @Override
    public final boolean isInModel(final TLCState s) {
        return this.tool.isInModel(s);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#isInActions(tlc2.tool.TLCState, tlc2.tool.TLCState)
     */
    @Override
    public final boolean isInActions(final TLCState s1, final TLCState s2) {
        return this.tool.isInActions(s1, s2);
    }

    /* Reconstruct the initial state whose fingerprint is fp. */
    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#getState(long)
     */
    @Override
    public final TLCStateInfo getState(final long fp) {
        return this.tool.getState(fp);
    }

    /* Reconstruct the next state of state s whose fingerprint is fp. */
    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#getState(long, tlc2.tool.TLCState)
     */
    @Override
    public final TLCStateInfo getState(final long fp, final TLCState s) {
        return this.tool.getState(fp, s);
    }

    /* Reconstruct the info for the transition from s to s1. */
    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#getState(tlc2.tool.TLCState, tlc2.tool.TLCState)
     */
    @Override
    public TLCStateInfo getState(final TLCState s1, final TLCState s) {
        return this.tool.getState(s1, s);
    }

    @Override
    public TLCStateInfo evalAlias(final TLCStateInfo current, final TLCState successor) {
        return this.tool.evalAlias(current, successor);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#setCallStack()
     */
    @Override
    public final void setCallStack() {
        this.tool = new CallStackTool(this.tool);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.DistApp#printCallStack()
     */
    @Override
    public final String printCallStack() {
        return this.tool.toString();
    }

    public FPSetConfiguration getFPSetConfiguration() {
        return fpSetConfig;
    }
}
