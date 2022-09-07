// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:57 PST by lamport  
//      modified on Fri Jul 27 10:47:59 PDT 2001 by yuanyu   
package tlc2.tool.distributed;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.function.Supplier;

import model.InJarFilenameToStream;
import model.ModelInJar;
import tlc2.TLCGlobals;
import tlc2.tool.Action;
import tlc2.tool.IStateFunctor;
import tlc2.tool.ITool;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.tool.WorkerException;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.impl.CallStackTool;
import tlc2.tool.impl.FastTool;
import tlc2.util.FP64;
import util.FileUtil;
import util.FilenameToStream;
import util.TLAConstants;
import util.ToolIO;
import util.UniqueString;

public class TLCApp extends DistApp {

	private String config;

	/* Constructors */
	public TLCApp(String specFile, String configFile, boolean deadlock,
			String fromChkpt, FPSetConfiguration fpSetConfig) throws IOException {
		this(specFile, configFile, deadlock, null);

		this.fromChkpt = fromChkpt;
		this.metadir = FileUtil.makeMetaDir(this.tool.getSpecDir(), fromChkpt);
		this.fpSetConfig = fpSetConfig;
	}
	
	public TLCApp(String specFile, String configFile, boolean deadlock,
			String fromChkpt, FPSetConfiguration fpSetConfig, FilenameToStream fts) throws IOException {
		this(specFile, configFile, deadlock, fts);

		this.fromChkpt = fromChkpt;
		this.metadir = FileUtil.makeMetaDir(this.tool.getSpecDir(), fromChkpt);
		this.fpSetConfig = fpSetConfig;
	}

	// TODO too many constructors redefinitions, replace with this(..) calls
	public TLCApp(String specFile, String configFile,
			Boolean deadlock, FilenameToStream fts) throws IOException {

		// get the spec dir from the spec file
		int lastSep = specFile.lastIndexOf(File.separatorChar);
		String specDir = (lastSep == -1) ? "" : specFile.substring(0,
				lastSep + 1);
		specFile = specFile.substring(lastSep + 1);
		
		this.config = configFile;
		
		
		this.checkDeadlock = deadlock.booleanValue();
		this.preprocess = true;
		this.tool = new FastTool(specDir, specFile, configFile, fts, new HashMap<>());

		this.impliedInits = this.tool.getImpliedInits();
		this.invariants = this.tool.getInvariants();
		this.impliedActions = this.tool.getImpliedActions();
		this.actions = this.tool.getActions();
	}

	/* Fields */
	public ITool tool;
	public Action[] invariants; // the invariants to be checked
	public Action[] impliedInits; // the implied-inits to be checked
	public Action[] impliedActions; // the implied-actions to be checked
	public Action[] actions; // the subactions
	private boolean checkDeadlock; // check deadlock?
	private final boolean preprocess; // preprocess?
	private String fromChkpt = null; // recover from this checkpoint
	private String metadir = null; // the directory pathname for metadata
	private FPSetConfiguration fpSetConfig;
   
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#getCheckDeadlock()
	 */
	public final Boolean getCheckDeadlock() {
		return new Boolean(this.checkDeadlock);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#getPreprocess()
	 */
	public final Boolean getPreprocess() {
		return new Boolean(this.preprocess);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#getFileName()
	 */
	public final String getFileName() {
		return this.tool.getRootFile();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#getSpecDir()
	 */
	public String getSpecDir() {
		return this.tool.getSpecDir();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#getConfigName()
	 */
	public String getConfigName() {
		return this.config;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#getMetadir()
	 */
	public final String getMetadir() {
		return this.metadir;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#canRecover()
	 */
	public final boolean canRecover() {
		return this.fromChkpt != null;
	}
	
	public List<File> getModuleFiles() {
		return this.tool.getModuleFiles(new InJarFilenameToStream(ModelInJar.PATH));
    }

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#getInitStates(tlc2.tool.IStateFunctor)
	 */
	public final void getInitStates(IStateFunctor functor) {
		this.tool.getInitStates(functor);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#getNextStates(tlc2.tool.TLCState)
	 */
	public final TLCState[] getNextStates(TLCState curState)
			throws WorkerException {
		StateVec nextStates = new StateVec(10);
		for (int i = 0; i < this.actions.length; i++) {
			Action curAction = this.actions[i];
			StateVec nstates = this.tool.getNextStates(curAction,
					(TLCState) curState);
			nextStates = nextStates.addElements(nstates);
		}
		int len = nextStates.size();
		if (len == 0 && this.checkDeadlock) {
			throw new WorkerException("Error: deadlock reached.", curState,
					null, false);
		}
		TLCState[] res = new TLCState[nextStates.size()];
		for (int i = 0; i < nextStates.size(); i++) {
			TLCState succState = nextStates.elementAt(i);
			if (!this.tool.isGoodState(succState)) {
				String msg = "Error: Successor state is not completely specified by"
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
	public final void checkState(TLCState s1, TLCState s2)
			throws WorkerException {
		TLCState ts2 = (TLCState) s2;
		for (int i = 0; i < this.invariants.length; i++) {
			if (!tool.isValid(this.invariants[i], ts2)) {
				// We get here because of invariant violation:
				String msg = "Error: Invariant " + this.tool.getInvNames()[i]
						+ " is violated.";
				throw new WorkerException(msg, s1, s2, false);
			}
		}
		if (s1 == null) {
			for (int i = 0; i < this.impliedInits.length; i++) {
				if (!this.tool.isValid(this.impliedInits[i], ts2)) {
					// We get here because of implied-inits violation:
					String msg = "Error: Implied-init "
							+ this.tool.getImpliedInitNames()[i]
							+ " is violated.";
					throw new WorkerException(msg, s1, s2, false);
				}
			}
		} else {
			TLCState ts1 = (TLCState) s1;
			for (int i = 0; i < this.impliedActions.length; i++) {
				if (!tool.isValid(this.impliedActions[i], ts1, ts2)) {
					// We get here because of implied-action violation:
					String msg = "Error: Implied-action "
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
	public final boolean isInModel(TLCState s) {
		return this.tool.isInModel((TLCState) s);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#isInActions(tlc2.tool.TLCState, tlc2.tool.TLCState)
	 */
	public final boolean isInActions(TLCState s1, TLCState s2) {
		return this.tool.isInActions((TLCState) s1, (TLCState) s2);
	}

	/* Reconstruct the initial state whose fingerprint is fp. */
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#getState(long)
	 */
	public final TLCStateInfo getState(long fp) {
		return this.tool.getState(fp);
	}

	/* Reconstruct the next state of state s whose fingerprint is fp. */
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#getState(long, tlc2.tool.TLCState)
	 */
	public final TLCStateInfo getState(long fp, TLCState s) {
		return this.tool.getState(fp, s);
	}

	/* Reconstruct the info for the transition from s to s1. */
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#getState(tlc2.tool.TLCState, tlc2.tool.TLCState)
	 */
	public TLCStateInfo getState(TLCState s1, TLCState s) {
		return this.tool.getState(s1, s);
	}
	
	@Override
	public TLCStateInfo evalAlias(TLCStateInfo current, TLCState successor, Supplier<List<TLCStateInfo>> prefix) {
		return this.tool.evalAlias(current, successor, prefix);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#setCallStack()
	 */
	public final void setCallStack() {
		this.tool = new CallStackTool(this.tool);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#printCallStack()
	 */
	public final String printCallStack() {
		return this.tool.toString();
	}

	@SuppressWarnings("deprecation")
	public static TLCApp create(String args[]) throws IOException {
		String specFile = null;
		String configFile = null;
		boolean deadlock = true;
		int fpIndex = 0;
		String fromChkpt = null;

		FPSetConfiguration fpSetConfig = new FPSetConfiguration();
		
		int index = 0;
		while (index < args.length) {
			if (args[index].equals("-config")) {
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
			} else if (args[index].equals("-tool")) {
				index++;
                TLCGlobals.tool = true;
			} else if (args[index].equals("-deadlock")) {
				index++;
				deadlock = false;
			} else if (args[index].equals("-recover")) {
				index++;
				if (index < args.length) {
					fromChkpt = args[index++] + FileUtil.separator;
				} else {
					printErrorMsg("Error: need to specify the metadata directory for recovery.");
					return null;
				}
			} else if (args[index].equals("-checkpoint")) {
				index++;
                if (index < args.length) {
					try {
						TLCGlobals.chkptDuration = Integer.parseInt(args[index]) * 1000 * 60;
						if (TLCGlobals.chkptDuration < 0) {
							printErrorMsg("Error: expect a nonnegative integer for -checkpoint option.");
						}

						index++;
					} catch (Exception e) {
						printErrorMsg("Error: An integer for checkpoint interval is required. But encountered "
								+ args[index]);
					}
				} else {
					printErrorMsg("Error: checkpoint interval required.");
				}
			} else if (args[index].equals("-coverage")) {
				index++;
				if (index < args.length) {
					try {
						// Coverage reporting is broken is distributed TLC. Thus
						// warn the user and continue ignoring the parameter.
						// Consume its value though.
						ToolIO.out.println(
								"Warning: coverage reporting not supported in distributed TLC, ignoring -coverage "
										+ args[index] + " parameter.");
//						TLCGlobals.coverageInterval = Integer
//						.parseInt(args[index]) * 1000;
//						if (TLCGlobals.coverageInterval < 0) {
//							printErrorMsg("Error: expect a nonnegative integer for -coverage option.");
//							return null;
//						}
						index++;
					} catch (Exception e) {
						printErrorMsg("Error: An integer for coverage report interval required."
								+ " But encountered " + args[index]);
						return null;
					}
				} else {
					printErrorMsg("Error: coverage report interval required.");
					return null;
				}
			} else if (args[index].equals("-terse")) {
				index++;
				TLCGlobals.expand = false;
			} else if (args[index].equals("-nowarning")) {
				index++;
				TLCGlobals.warn = false;
            } else if (args[index].equals("-maxSetSize"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                        int bound = Integer.parseInt(args[index]);
                        
                    	// make sure it's in valid range
                    	if (!TLCGlobals.isValidSetSize(bound)) {
                    		int maxValue = Integer.MAX_VALUE;
                    		printErrorMsg("Error: Value in interval [0, " + maxValue + "] for maxSetSize required. But encountered " + args[index]);
                    		return null;
                    	}
                    	TLCGlobals.setBound = bound;

                    	index++;
                    } catch (Exception e)
                    {
                        printErrorMsg("Error: An integer for maxSetSize required. But encountered " + args[index]);
                        return null;
                    }
                } else
                {
                    printErrorMsg("Error: maxSetSize required.");
                    return null;
                }
			} else if (args[index].equals("-fp")) {
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
					} catch (Exception e) {
						printErrorMsg("Error: A number for -fp is required. But encountered "
								+ args[index]);
						return null;
					}
				} else {
					printErrorMsg("Error: expect an integer for -workers option.");
					return null;
				}
				
				
			} else if (args[index].equals("-fpbits")) {
				index++;
				if (index < args.length) {
					try {
						int fpBits = Integer.parseInt(args[index]);
						
                    	// make sure it's in valid range
                    	if (!FPSet.isValid(fpBits)) {
                    		printErrorMsg("Error: Value in interval [0, 30] for fpbits required. But encountered " + args[index]);
                    		return null;
                    	}
                    	fpSetConfig.setFpBits(fpBits);
                    	
						index++;
					} catch (Exception e) {
						printErrorMsg("Error: A number for -fpbits is required. But encountered "
								+ args[index]);
						return null;
					}
				} else {
					printErrorMsg("Error: expect an integer for -workers option.");
					return null;
				}
            } else if (args[index].equals("-fpmem"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
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
                    	double fpmem = Double.parseDouble(args[index]);
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
                    } catch (Exception e)
                    {
                        printErrorMsg("Error: A positive integer or a fraction for fpset memory size/percentage required. But encountered " + args[index]);
                        return null;
                    }
                }
			} else if (args[index].equals("-metadir")) {
				index++;
                if (index < args.length)
                {
                    TLCGlobals.metaDir = args[index++] + FileUtil.separator;
                } else {
                    printErrorMsg("Error: need to specify the metadata directory.");
                    return null;
                }
            } else {
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

		if (specFile == null) {
			// command line omitted name of spec file, take this as an
			// indicator to check the in-jar model/ folder for a spec.
			// If a spec is found, use it instead.
			if (ModelInJar.hasModel()) {
				ModelInJar.loadProperties(); // Reads result.mail.address and so on.
				TLCGlobals.tool = true; // always run in Tool mode (to parse output by Toolbox later)
				TLCGlobals.chkptDuration = 0; // never use checkpoints with distributed TLC (highly inefficient)
				FP64.Init(fpIndex);
				FilenameToStream resolver = new InJarFilenameToStream(ModelInJar.PATH);
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

	private static void printErrorMsg(String msg) {
		ToolIO.out.println(msg);
		ToolIO.out
				.println("Usage: java tlc2.tool.TLCServer [-option] inputfile");
	}

	public FPSetConfiguration getFPSetConfiguration() {
		return fpSetConfig;
	}
}
