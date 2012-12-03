// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:57 PST by lamport  
//      modified on Fri Jul 27 10:47:59 PDT 2001 by yuanyu   

package tlc2.tool.distributed;

import java.io.File;
import java.io.IOException;

import tlc2.TLCGlobals;
import tlc2.tool.Action;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.tool.Tool;
import tlc2.tool.WorkerException;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.util.FP64;
import tlc2.value.Value;
import util.FileUtil;
import util.FilenameToStream;
import util.ToolIO;
import util.UniqueString;

/**
 * @version $Id$
 */
public class TLCApp extends DistApp {

	private String config;

	/* Constructors */
	public TLCApp(String specFile, String configFile, boolean deadlock,
			String fromChkpt, FPSetConfiguration fpSetConfig) throws IOException {
		this(specFile, configFile, deadlock, true, null);

		this.fromChkpt = fromChkpt;
		this.metadir = FileUtil.makeMetaDir(this.tool.specDir, fromChkpt);
		this.fpSetConfig = fpSetConfig;
	}

	// TODO too many constructors redefinitions, replace with this(..) calls
	public TLCApp(String specFile, String configFile,
			Boolean deadlock, Boolean preprocess, FilenameToStream fts) throws IOException {

		// get the spec dir from the spec file
		int lastSep = specFile.lastIndexOf(File.separatorChar);
		String specDir = (lastSep == -1) ? "" : specFile.substring(0,
				lastSep + 1);
		specFile = specFile.substring(lastSep + 1);
		
		this.config = configFile;
		
		// TODO NameResolver
		this.tool = new Tool(specDir, specFile, configFile, fts);
		// SZ Feb 24, 2009: setup the user directory
		ToolIO.setUserDir(specDir);

		this.checkDeadlock = deadlock.booleanValue();
		this.preprocess = preprocess.booleanValue();
		// SZ Feb 20, 2009: added null reference to SpecObj
		this.tool.init(this.preprocess, null);
		this.impliedInits = this.tool.getImpliedInits();
		this.invariants = this.tool.getInvariants();
		this.impliedActions = this.tool.getImpliedActions();
		this.actions = this.tool.getActions();
	}

	/* Fields */
	public Tool tool;
	public Action[] invariants; // the invariants to be checked
	public Action[] impliedInits; // the implied-inits to be checked
	public Action[] impliedActions; // the implied-actions to be checked
	public Action[] actions; // the subactions
	private boolean checkDeadlock; // check deadlock?
	private boolean preprocess; // preprocess?
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
		return this.tool.rootFile;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#getSpecDir()
	 */
	public String getSpecDir() {
		return this.tool.specDir;
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

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#getInitStates()
	 */
	public final TLCState[] getInitStates() throws WorkerException {
		StateVec theInitStates = this.tool.getInitStates();
		TLCState[] res = new TLCState[theInitStates.size()];
		for (int i = 0; i < theInitStates.size(); i++) {
			TLCState curState = theInitStates.elementAt(i);
			if (!this.tool.isGoodState(curState)) {
				String msg = "Error: Initial state is not completely specified by the"
						+ " initial predicate.";
				throw new WorkerException(msg, curState, null, false);
			}
			res[i] = (TLCState) curState;
		}
		return res;
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

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#setCallStack()
	 */
	public final void setCallStack() {
		this.tool.setCallStack();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.DistApp#printCallStack()
	 */
	public final String printCallStack() {
		// SZ Jul 10, 2009: check if this is ok
		// changed the method signature
		return this.tool.getCallStack().toString();
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
					int len = configFile.length();
					if (configFile.startsWith(".cfg", len - 4)) {
						configFile = configFile.substring(0, len - 4);
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
						TLCGlobals.coverageInterval = Integer
								.parseInt(args[index]) * 1000;
						if (TLCGlobals.coverageInterval < 0) {
							printErrorMsg("Error: expect a nonnegative integer for -coverage option.");
							return null;
						}
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
				Value.expand = false;
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
				int len = specFile.length();
				if (specFile.startsWith(".tla", len - 4)) {
					specFile = specFile.substring(0, len - 4);
				}
			}
		}

		if (specFile == null) {
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
