// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Thu 10 April 2008 at 14:31:23 PST by lamport 
//      modified on Wed Dec  5 22:37:20 PST 2001 by yuanyu 

package tlc2;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TimeZone;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import model.InJarFilenameToStream;
import model.ModelInJar;
import tlc2.debug.TLCDebugger;
import tlc2.output.EC;
import tlc2.output.ErrorTraceMessagePrinterRecorder;
import tlc2.output.MP;
import tlc2.output.Messages;
import tlc2.tool.DFIDModelChecker;
import tlc2.tool.ITool;
import tlc2.tool.ModelChecker;
import tlc2.tool.Simulator;
import tlc2.tool.SingleThreadedSimulator;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.FPSetFactory;
import tlc2.tool.impl.DebugTool;
import tlc2.tool.impl.FastTool;
import tlc2.tool.impl.Tool;
import tlc2.tool.management.ModelCheckerMXWrapper;
import tlc2.tool.management.TLCStandardMBean;
import tlc2.util.DotStateWriter;
import tlc2.util.FP64;
import tlc2.util.IStateWriter;
import tlc2.util.NoopStateWriter;
import tlc2.util.RandomGenerator;
import tlc2.util.StateWriter;
import tlc2.value.RandomEnumerableValues;
import util.Assert.TLCRuntimeException;
import util.DebugPrinter;
import util.ExecutionStatisticsCollector;
import util.FileUtil;
import util.FilenameToStream;
import util.MailSender;
import util.SimpleFilenameToStream;
import util.TLAConstants;
import util.TLCRuntime;
import util.ToolIO;
import util.UniqueString;
import util.UsageGenerator;

/**
 * Main TLC starter class.
 * 
 * <b>Note:</b> If you are using a new instance of this class in an already existant JVM which has done processing with
 * 			tlc2 parsers, please see the class javadocs for {@link TLCRunner}
 * 
 * @author Yuan Yu
 * @author Leslie Lamport
 * @author Simon Zambrovski
 */
public class TLC {
	/**
	 * Whether the TLA+ spec is encoded in a .jar file, not a TLA+ text file.
	 */
    private static boolean MODEL_PART_OF_JAR = false;
    
    /**
     * Possible TLC run modes: either model checking or simulation.
     */
    public enum RunMode {
    	MODEL_CHECK, SIMULATE;
    }
    

    // SZ Feb 20, 2009: the class has been 
    // transformed from static to dynamic

    /**
     * Whether to run in model checking or simulation mode.
     * Defaults to model checking.
     */
    private RunMode runMode;
    /**
     * Whether to clean up the states directory.
     */
    private boolean cleanup;
    /**
     * Whether to check for deadlock.
     */
    private boolean deadlock;

    /**
     * Whether a seed for the random number generator was provided.
     */
    private boolean noSeed;
    /**
     * The seed for the random number generator.
     */
    private long seed;
    /**
     * Adjustment for random number generator seed.
     */
    private long aril;
    
    /**
     * TLC processing start time.
     */
	private long startTime;

	/**
	 * Name of main TLA+ specification file.
	 */
    private String mainFile;
    private String configFile;
	private String metadir;
    /**
	 * If instantiated with a non-Noop* instance, the trace will be written to the
	 * user provided file (-dump parameter).
	 * <p>
	 * Contrary to plain -dump, -dot will also write out transitions from state s to
	 * s' if s' is already known. Thus, the resulting graph shows all successors of
	 * s instead of just s's unexplored ones.
	 * <p>
	 * Off (NoopStateWriter) by default.
	 */
    private IStateWriter stateWriter = new NoopStateWriter();

    /**
     * Name of checkpoint from which TLC should recover.
     */
    private String fromChkpt;

    /**
     * Fingerprint set function index to use.
     * By default one is picked at random.
     */
    private int fpIndex;
    /**
     * The number of traces/behaviors to generate in simulation mode
     */
    private static long traceNum = Long.MAX_VALUE;

    /**
     * Name of the file to which to write state traces.
     */
    private String traceFile = null;
    private String traceActions = null;
    /**
     * Maximum state trace depth. Set to 100 by default.
     */
    private int traceDepth;
    private FilenameToStream resolver;

    /**
	 * Whether welcome message has already been printed.
	 */
    private boolean welcomePrinted;
    
    /**
     * Fingerprint set configuration.
     */
    private FPSetConfiguration fpSetConfiguration;
    
    private int debugPort = -1;
    private boolean suspend = true;
    private boolean halt = true;
    
    /**
     * Interface to retrieve model properties.
     */
    private volatile ITool tool;

    /**
     * Records errors as TLC runs.
     */
    private final ErrorTraceMessagePrinterRecorder recorder = new ErrorTraceMessagePrinterRecorder();
    
    /**
     * Trace exploration spec generator.
     */
    private TraceExplorationSpec teSpec;
    
    /**
     * Initialization
     */
	public TLC() {
        welcomePrinted = false;
        
        runMode = RunMode.MODEL_CHECK;
        cleanup = false;
        deadlock = true;
        
        noSeed = true;
        seed = 0;
        aril = 0;
        
        mainFile = null;
        configFile = null;
        fromChkpt = null;
        resolver = null;

        fpIndex = new Random().nextInt(FP64.Polys.length);
        traceDepth = 100;

        fpSetConfiguration = new FPSetConfiguration();
	}

    /*
     * This TLA checker (TLC) provides the following functionalities:
     *  1. Simulation of TLA+ specs:
     *  				java tlc2.TLC -simulate spec[.tla]
     *  2. Model checking of TLA+ specs:
     *  				java tlc2.TLC [-modelcheck] spec[.tla]
     *
     * The command line also provides the following options observed for functionalities 1. & 2.:
     *  o -config file: provide the config file.
     *		Defaults to spec.cfg if not provided
     *  o -deadlock: do not check for deadlock.
     *		Defaults to checking deadlock if not specified
     *  o -depth num: specify the depth of random simulation 
     *		Defaults to 100 if not specified
     *  o -seed num: provide the seed for random simulation
     *		Defaults to a random seed if not specified
     *  o -aril num: Adjust the seed for random simulation
     *		Defaults to 0 if not specified
     *  o -recover path: recover from the checkpoint at path
     *		Defaults to scratch run if not specified
     *  o -metadir path: store metadata in the directory at path
     *		Defaults to specdir/states if not specified
	 *  o -userFile file: A full qualified/absolute path to a file to log user
	 *					output (Print/PrintT/...) to
     *  o -workers num: the number of TLC worker threads
     *		Defaults to 1
     *  o -dfid num: use depth-first iterative deepening with initial depth num
     *  o -cleanup: clean up the states directory
     *  o -dump [dot] file: dump all the states into file. If "dot" as sub-parameter
     *					is given, the output will be in dot notation.
     *  o -difftrace: when printing trace, show only
     *					the differences between successive states
     *		Defaults to printing full state descriptions if not specified
     *					(Added by Rajeev Joshi)
     *  o -terse: do not expand values in Print statement
     *		Defaults to expand value if not specified
     *  o -coverage minutes: collect coverage information on the spec,
     *					print out the information every minutes.
     *		Defaults to no coverage if not specified
     *  o -continue: continue running even when invariant is violated
     *		Defaults to stop at the first violation if not specified
     *  o -lncheck: Check liveness properties at different times
     *					of model checking.
     *		Defaults to false increasing the overall model checking time.
     *  o -nowarning: disable all the warnings
     *		Defaults to report warnings if not specified
     *  o -fp num: use the num'th irreducible polynomial from the list
     *					stored in the class FP64.
     *  o -view: apply VIEW (if provided) when printing out states.
     *  o -gzip: control if gzip is applied to value input/output stream.
     *		Defaults to off if not specified
     *  o -debug: debbuging information (non-production use)
     *  o -debugger: Activate TLC debugger
     *  o -tool: tool mode (put output codes on console)
     *  o -generateSpecTE: will generate SpecTE assets if error-states are
     *  				encountered during model checking; this will change
     *  				to tool mode regardless of whether '-tool' was
     *  				explicitly specified; add on 'nomonolith' to not
     *  				embed the dependencies in the SpecTE
     *  o -checkpoint num: interval for check pointing (in minutes)
     *		Defaults to 30
     *  o -fpmem num: a value between 0 and 1, exclusive, representing the ratio
     *  				of total system memory used to store the fingerprints of
     *  				found states.
     *  	Defaults to 1/4 physical memory.  (Added 6 Apr 2010 by Yuan Yu.)
     *  o -fpbits num: the number of msb used by MultiFPSet to create nested FPSets.
     *  	Defaults to 1
     *  o -maxSetSize num: the size of the largest set TLC will enumerate.
     *		Defaults to 1000000
     *   
     */
    public static void main(String[] args) throws Exception
    {
        final TLC tlc = new TLC();

        // Try to parse parameters.
        if (!tlc.handleParameters(args)) {
            // This is a tool failure. We must exit with a non-zero exit
            // code or else we will mislead system tools and scripts into
            // thinking everything went smoothly.
            //
            // FIXME: handleParameters should return an error object (or
            // null), where the error object contains an error message.
            // This makes handleParameters a function we can test.
            System.exit(1);
        }
        
        if (!tlc.checkEnvironment()) {
            System.exit(1);
        }

		final MailSender ms = new MailSender();
		// Setup how spec files will be resolved in the filesystem.
		if (MODEL_PART_OF_JAR) {
			// There was not spec file given, it instead exists in the
			// .jar file being executed. So we need to use a special file
			// resolver to parse it.
			tlc.setResolver(new InJarFilenameToStream(ModelInJar.PATH));
		} else {
			// The user passed us a spec file directly. To ensure we can
			// recover it during semantic parsing, we must include its
			// parent directory as a library path in the file resolver.
			//
			// If the spec file has no parent directory, use the "standard"
			// library paths provided by SimpleFilenameToStream.
			final String dir = FileUtil.parseDirname(tlc.getMainFile());
			if (!dir.isEmpty()) {
				tlc.setResolver(new SimpleFilenameToStream(dir));
			} else {
				tlc.setResolver(new SimpleFilenameToStream());
			}
		}

		// Setup MailSender *before* calling tlc.process. The MailSender's task it to
		// write the MC.out file. The MC.out file is e.g. used by CloudTLC to feed
		// progress back to the Toolbox (see CloudDistributedTLCJob).
		ms.setModelName(tlc.getModelName());
		ms.setSpecName(tlc.getSpecName());

        // Execute TLC.
        final int errorCode = tlc.process();

        // Send logged output by email.
        //
        // This is needed when TLC runs on another host and email is
        // the only means for the user to get access to the model
        // checking results.
        boolean mailSent = ms.send(tlc.getModuleFiles());

        // Treat failure to send mail as a tool failure.
        //
        // With distributed TLC and CloudDistributedTLCJob in particular,
        // the cloud node is immediately turned off once the TLC process
        // has finished. If we were to shutdown the node even when sending
        // out the email has failed, the result would be lost.
        if (!mailSent) {
            System.exit(1);
        }

        // Be explicit about tool success.
        System.exit(EC.ExitStatus.errorConstantToExitStatus(errorCode));
    }
    
	// false if the environment (JVM, OS, ...) makes model checking impossible.
	// Might also result in warnings.
	private boolean checkEnvironment() {
		// Not a reasons to refuse startup but warn about non-ideal garbage collector.
		// See https://twitter.com/lemmster/status/1089656514892070912 for actual
		// performance penalty.
		if (!TLCRuntime.getInstance().isThroughputOptimizedGC()) {
			MP.printWarning(EC.TLC_ENVIRONMENT_JVM_GC);
		}
		
		return true;
	}

	public static void setTraceNum(long aTraceNum) {
		traceNum = aTraceNum;
	}

    /**
     * This method handles parameter arguments and prepares the actual call
     * <strong>Note:</strong> This method set ups the static TLCGlobals variables
     * @return status of parsing: true iff parameter check was ok, false otherwise
     * @throws IOException 
     */
    // SZ Feb 23, 2009: added return status to indicate the error in parsing
	@SuppressWarnings("deprecation")	// we're emitting a warning to the user, but still accepting fpmem values > 1
	public boolean handleParameters(String[] args)
    {
		String dumpFile = null;
		boolean asDot = false;
	    boolean colorize = false;
	    boolean actionLabels = false;
		boolean snapshot = false;
		
		boolean generateTESpec = true;
		Path teSpecOutDir = null;
		
        // SZ Feb 20, 2009: extracted this method to separate the 
        // parameter handling from the actual processing
        int index = 0;
		while (index < args.length)
        {
            if (args[index].equals("-simulate") || args[index].equals("-generate"))
            {
            	if (args[index].equals("-generate")) {
					System.setProperty(Tool.class.getName() + ".probabilistic", Boolean.TRUE.toString());
            	}
            	runMode = RunMode.SIMULATE;
                index++;
                
				// Simulation args can be:
				// file=/path/to/file,num=4711 or num=4711,file=/path/to/file or num=4711 or
				// file=/path/to/file
				// "file=..." and "num=..." are only relevant for simulation which is why they
				// are args to "-simulate".
				if ((index < args.length) && (args[index].contains("stats=") || args[index].contains("file=")
						|| args[index].contains("num="))) {
					final String[] simArgs = args[index].split(",");
					index++; // consume simulate args
					for (String arg : simArgs) {
						if (arg.startsWith("num=")) {
							traceNum = Long.parseLong(arg.replace("num=", ""));
						} else if (arg.startsWith("file=")) {
							traceFile = arg.replace("file=", "");
						} else if (arg.equals("stats=basic")) {
							traceActions = "BASIC";
						} else if (arg.equals("stats=full")) {
							traceActions = "FULL";
						}
					}
				}
			} else if (args[index].equals("-modelcheck")) {
				index++;
            } else if (args[index].equals("-difftrace"))
            {
                index++;
                TLCGlobals.printDiffsOnly = true;
            } else if (args[index].equals("-deadlock"))
            {
                index++;
                deadlock = false;
            } else if (args[index].equals("-cleanup"))
            {
                index++;
                cleanup = true;
            } else if (args[index].equals("-nowarning"))
            {
                index++;
                TLCGlobals.warn = false;
            } else if (args[index].equals("-gzip"))
            {
                index++;
                TLCGlobals.useGZIP = true;
            } else if (args[index].equals("-terse"))
            {
                index++;
                TLCGlobals.expand = false;
            } else if (args[index].equals("-continue"))
            {
                index++;
                TLCGlobals.continuation = true;
            } else if (args[index].equals("-view"))
            {
                index++;
                TLCGlobals.useView = true;
            } else if (args[index].equals("-debug"))
            {
                index++;
                TLCGlobals.debug = true;
            } else if (args[index].equals("-debugger"))
            {
                index++;
                debugPort = 4712;  //standard port.
				if ((index < args.length) && (args[index].contains("port=") || args[index].contains("nosuspend")
						|| args[index].contains("nohalt"))) {
					suspend = !args[index].toLowerCase().contains("nosuspend");
					halt = !args[index].toLowerCase().contains("nohalt");

					final Matcher matcher = Pattern.compile(".*port=([0-9]{1,5}).*").matcher(args[index]);
					if (matcher.find()) {
						debugPort = Integer.parseInt(matcher.group(1));
					}
					index++;
				}
            } else if (args[index].equals("-tool"))
            {
                index++;
                TLCGlobals.tool = true;
            } else if (args[index].equals("-generateSpecTE")) {
                index++;
                if ((index < args.length) && args[index].equals("nomonolith")) {
                	index++;
                }
            } else if (args[index].equals("-noGenerateSpecTE"))
            {
            	index++;
            	generateTESpec = false;
            } else if (args[index].equals("-teSpecOutDir"))
            {
            	index++;
            	if (index < args.length) {
            		String path = args[index];
            		try {
						teSpecOutDir = Paths.get(path);
            		} catch (InvalidPathException e) {
            			printErrorMsg("Error: invalid path for -teSpecOutDir option: " + path);
            			return false;
            		}

            		index++;
            	} else {
            		printErrorMsg("Error: expected a path for -teSpecOutDir option.");
            		return false;
            	}
            } else if (args[index].equals("-help") || args[index].equals("-h"))
            {
            	// See note referring to "-help" in MP#getMessage0 for EC.WRONG_COMMANDLINE_PARAMS_TLC.
                printUsage();
                return false;
            } else if (args[index].equals("-lncheck"))
            {
                index++;
                if (index < args.length)
                {
                    TLCGlobals.lnCheck = args[index].toLowerCase();
                    index++;
                } else
                {
                    printErrorMsg("Error: expect a strategy such as final for -lncheck option.");
                    return false;
                }
           } else if (args[index].equals("-config"))
            {
                index++;
                if (index < args.length)
                {
                    configFile = args[index];
					if (configFile.endsWith(TLAConstants.Files.CONFIG_EXTENSION)) {
						configFile = configFile.substring(0,
								(configFile.length() - TLAConstants.Files.CONFIG_EXTENSION.length()));
					}
                    index++;
                } else
                {
                    printErrorMsg("Error: expect a file name for -config option.");
                    return false;
                }
            } else if (args[index].equals("-dump"))
            {
                index++; // consume "-dump".
                if (((index + 1) < args.length) && args[index].startsWith("dot"))
                {
                	final String dotArgs = args[index].toLowerCase();
                	index++; // consume "dot...".
                	asDot = true;
                	colorize = dotArgs.contains("colorize");
                	actionLabels = dotArgs.contains("actionlabels");
                	snapshot = dotArgs.contains("snapshot");
					dumpFile = getDumpFile(args[index++], ".dot");
                }
                else if (index < args.length)
                {
					dumpFile = getDumpFile(args[index++], ".dump");
                } else
                {
                    printErrorMsg("Error: A file name for dumping states required.");
                    return false;
                }
            } else if (args[index].equals("-coverage"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                        TLCGlobals.coverageInterval = Integer.parseInt(args[index]) * 60 * 1000;
                        if (TLCGlobals.coverageInterval < 0)
                        {
                            printErrorMsg("Error: expect a nonnegative integer for -coverage option.");
                            return false;
                        }
                        index++;
                    } catch (NumberFormatException e)
                    {
                        
                        printErrorMsg("Error: An integer for coverage report interval required." + " But encountered "
                                + args[index]);
                        return false;
                    }
                } else
                {
                    printErrorMsg("Error: coverage report interval required.");
                    return false;
                }
            } else if (args[index].equals("-checkpoint"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                        TLCGlobals.chkptDuration = Integer.parseInt(args[index]) * 1000 * 60;
                        if (TLCGlobals.chkptDuration < 0)
                        {
                            printErrorMsg("Error: expect a nonnegative integer for -checkpoint option.");
                            return false;
                        }
                        
                        index++;
                    } catch (Exception e)
                    {
                        printErrorMsg("Error: An integer for checkpoint interval is required. But encountered " + args[index]);
                        return false;
                    }
                } else
                {
                    printErrorMsg("Error: checkpoint interval required.");
                    return false;
                }
            } else if (args[index].equals("-depth"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                        traceDepth = Integer.parseInt(args[index]);
                        index++;
                    } catch (Exception e)
                    {
                        printErrorMsg("Error: An integer for trace length required. But encountered " + args[index]);
                        return false;
                    }
                } else
                {
                    printErrorMsg("Error: trace length required.");
                    return false;
                }
            } else if (args[index].equals("-seed"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                        seed = Long.parseLong(args[index]);
                        index++;
                        noSeed = false;
                    } catch (Exception e)
                    {
                        printErrorMsg("Error: An integer for seed required. But encountered " + args[index]);
                        return false;
                    }
                } else
                {
                    printErrorMsg("Error: seed required.");
                    return false;
                }
            } else if (args[index].equals("-aril"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                        aril = Long.parseLong(args[index]);
                        index++;
                    } catch (Exception e)
                    {
                        printErrorMsg("Error: An integer for aril required. But encountered " + args[index]);
                        return false;
                    }
                } else
                {
                    printErrorMsg("Error: aril required.");
                    return false;
                }
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
                    		return false;
                    	}
                    	TLCGlobals.setBound = bound;

                    	index++;
                    } catch (Exception e)
                    {
                        printErrorMsg("Error: An integer for maxSetSize required. But encountered " + args[index]);
                        return false;
                    }
                } else
                {
                    printErrorMsg("Error: maxSetSize required.");
                    return false;
                }
            } else if (args[index].equals("-recover"))
            {
                index++;
                if (index < args.length)
                {
                    fromChkpt = args[index++] + FileUtil.separator;
                } else
                {
                    printErrorMsg("Error: need to specify the metadata directory for recovery.");
                    return false;
                }
            } else if (args[index].equals("-metadir"))
            {
                index++;
                if (index < args.length)
                {
                    TLCGlobals.metaDir = args[index++] + FileUtil.separator;
                } else
                {
                    printErrorMsg("Error: need to specify the metadata directory.");
                    return false;
                }
            } else if (args[index].equals("-userFile"))
            {
                index++;
                if (index < args.length)
                {
                    try {
						// Most problems will only show when TLC eventually tries
						// to write to the file.
						tlc2.module.TLC.OUTPUT = new BufferedWriter(new FileWriter(new File(args[index++])));
        			} catch (IOException e) {
                        printErrorMsg("Error: Failed to create user output log file.");
                        return false;
        			}
                } else
                {
                    printErrorMsg("Error: need to specify the full qualified file.");
                    return false;
                }
            } else if (args[index].equals("-workers"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                        int num = args[index].trim().toLowerCase().equals("auto")
                                ? Runtime.getRuntime().availableProcessors()
                                : Integer.parseInt(args[index]);
                        if (num < 1)
                        {
                            printErrorMsg("Error: at least one worker required.");
                            return false;
                        }
                        TLCGlobals.setNumWorkers(num);
                        index++;
                    } catch (Exception e)
                    {
                        printErrorMsg("Error: worker number or 'auto' required. But encountered " + args[index]);
                        return false;
                    }
                } else
                {
                    printErrorMsg("Error: expect an integer or 'auto' for -workers option.");
                    return false;
                }
            } else if (args[index].equals("-dfid"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                        TLCGlobals.DFIDMax = Integer.parseInt(args[index]);
                        if (TLCGlobals.DFIDMax < 0)
                        {
                            printErrorMsg("Error: expect a nonnegative integer for -dfid option.");
                            return false;
                        }
                        index++;
                    } catch (Exception e)
                    {
                        printErrorMsg("Error: expect a nonnegative integer for -dfid option. " + "But encountered "
                                + args[index]);
                        return false;
                    }
                } else
                {
                    printErrorMsg("Error: expect a nonnegative integer for -dfid option.");
                    return false;
                }
            } else if (args[index].equals("-fp"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                        fpIndex = Integer.parseInt(args[index]);
                        if (fpIndex < 0 || fpIndex >= FP64.Polys.length)
                        {
                            printErrorMsg("Error: The number for -fp must be between 0 and " + (FP64.Polys.length - 1)
                                    + " (inclusive).");
                            return false;
                        }
                        index++;
                    } catch (Exception e)
                    {
                        printErrorMsg("Error: A number for -fp is required. But encountered " + args[index]);
                        return false;
                    }
                } else
                {
                    printErrorMsg("Error: expect an integer for -fp option.");
                    return false;
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
                        double fpMemSize = Double.parseDouble(args[index]);
                        if (fpMemSize < 0) {
                            printErrorMsg("Error: An positive integer or a fraction for fpset memory size/percentage required. But encountered " + args[index]);
                            return false;
                        } else if (fpMemSize > 1) {
							// For legacy reasons we allow users to set the
							// absolute amount of memory. If this is the case,
							// we know the user intends to allocate all 100% of
							// the absolute memory to the fpset.
                    		ToolIO.out
            				.println("Using -fpmem with an abolute memory value has been deprecated. " +
            						"Please allocate memory for the TLC process via the JVM mechanisms " +
            						"and use -fpmem to set the fraction to be used for fingerprint storage.");
                        	fpSetConfiguration.setMemory((long) fpMemSize);
                        	fpSetConfiguration.setRatio(1.0d);
                        } else {
                    		fpSetConfiguration.setRatio(fpMemSize);
                        }
                        index++;
                    } catch (Exception e)
                    {
                        printErrorMsg("Error: An positive integer or a fraction for fpset memory size/percentage required. But encountered " + args[index]);
                        return false;
                    }
                } else
                {
                    printErrorMsg("Error: fpset memory size required.");
                    return false;
                }
            } else if (args[index].equals("-fpbits"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                    	int fpBits = Integer.parseInt(args[index]);

                    	// make sure it's in valid range
                    	if (!FPSet.isValid(fpBits)) {
                    		printErrorMsg("Error: Value in interval [0, 30] for fpbits required. But encountered " + args[index]);
                    		return false;
                    	}
                    	fpSetConfiguration.setFpBits(fpBits);
                    	
                        index++;
                    } catch (Exception e)
                    {
                        printErrorMsg("Error: An integer for fpbits required. But encountered " + args[index]);
                        return false;
                    }
                } else
                {
                    printErrorMsg("Error: fpbits required.");
                    return false;
                }
            } else
            {
                if (args[index].charAt(0) == '-')
                {
                    printErrorMsg("Error: unrecognized option: " + args[index]);
                    return false;
                }
                if (mainFile != null)
                {
                    printErrorMsg("Error: more than one input files: " + mainFile + " and " + args[index]);
                    return false;
                }
                mainFile = args[index++];
                if (mainFile.endsWith(TLAConstants.Files.TLA_EXTENSION))
                {
                    mainFile = mainFile.substring(0, (mainFile.length() - TLAConstants.Files.TLA_EXTENSION.length()));
                }
            }
        }
                
        startTime = System.currentTimeMillis();

		generateTESpec =
				generateTESpec
				&& !TLCGlobals.continuation
				&& !TLCGlobals.tool
				&& !TraceExplorationSpec.isTESpecFile(mainFile);
                
		if (generateTESpec) {
			final Path specDir = teSpecOutDir == null ? getTlaFileParentDir(mainFile) : teSpecOutDir;
			this.teSpec = new TraceExplorationSpec(specDir, new Date(startTime), this.recorder);
		}
		
		if (mainFile == null) {
			// command line omitted name of spec file, take this as an
			// indicator to check the in-jar model/ folder for a spec.
			// If a spec is found, use it instead.
			if (ModelInJar.hasModel()) {
				MODEL_PART_OF_JAR = true;
				ModelInJar.loadProperties();
				TLCGlobals.tool = true; // always run in Tool mode (to parse output by Toolbox later)
				TLCGlobals.chkptDuration = 0; // never use checkpoints with distributed TLC (highly inefficient)
				mainFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
			} else {
				printErrorMsg("Error: Missing input TLA+ module.");
				return false;
			}
		}

		// The functionality to start TLC from an (absolute) path /path/to/spec/file.tla
		// seems to have eroded over the years which is why this block of code is a
		// clutch. It essentially massages the variable values for mainFile, specDir and
		// the user dir to make the code below - as well as the FilenameToStream
		// resolver -
		// work. Original issues was https://github.com/tlaplus/tlaplus/issues/24.
		final File f = new File(mainFile);
		String specDir = "";
		if (f.isAbsolute()) {
			specDir = f.getParent() + FileUtil.separator;
			mainFile = f.getName();
			// Not setting user dir causes a ConfigFileException when the resolver
			// tries to read the .cfg file later in the game.
			ToolIO.setUserDir(specDir);
		}

		if (configFile == null) {
			configFile = mainFile;
		}

		if (cleanup && (fromChkpt == null)) {
			// clean up the states directory only when not recovering
			FileUtil.deleteDir(TLCGlobals.metaRoot, true);
		}

        // Check if mainFile is an absolute or relative file system path. If it is
		// absolute, the parent gets used as TLC's meta directory (where it stores
		// states...). Otherwise, no meta dir is set causing states etc. to be stored in
		// the current directory.
    	metadir = FileUtil.makeMetaDir(new Date(startTime), specDir, fromChkpt);
    	
		if (dumpFile != null) {
			if (dumpFile.startsWith("${metadir}")) {
				// prefix dumpfile with the known value of this.metadir. There
				// is no way to determine the actual value of this.metadir
				// before TLC startup and thus it's impossible to make the
				// dumpfile end up in the metadir if desired.
				dumpFile = dumpFile.replace("${metadir}", metadir);
			}
			try {
				if (asDot) {
					this.stateWriter = new DotStateWriter(dumpFile, colorize, actionLabels, snapshot);
				} else {
					this.stateWriter = new StateWriter(dumpFile);
				}
			} catch (IOException e) {
				printErrorMsg(String.format("Error: Given file name %s for dumping states invalid.", dumpFile));
				return false;
			}
		}
        
		if (TLCGlobals.debug) {
			final StringBuilder buffer = new StringBuilder("TLC arguments:");
			for (int i = 0; i < args.length; i++) {
				buffer.append(args[i]);
				if (i < args.length - 1) {
					buffer.append(" ");
				}
			}
			buffer.append("\n");
			DebugPrinter.print(buffer.toString());
		}
        
        // if no errors, print welcome message
        printWelcome();
        
        return true;
	}

	/**
	 * Require a $suffix file extension unless already given. It is not clear why
	 * this is enforced.
	 */
	private static String getDumpFile(String dumpFile, String suffix) {
		if (dumpFile.endsWith(suffix)) {
			return dumpFile;
		}
		return dumpFile + suffix;
	}

	/**
     * The processing method
     */
    public int process()
    {
    	MP.setRecorder(this.recorder);
        // UniqueString.initialize();
        
        // a JMX wrapper that exposes runtime statistics 
        TLCStandardMBean modelCheckerMXWrapper = TLCStandardMBean.getNullTLCStandardMBean();
        
		// SZ Feb 20, 2009: extracted this method to separate the 
        // parameter handling from the actual processing
        try
        {
            // Initialize:
            if (fromChkpt != null)
            {
                // We must recover the intern var table as early as possible
                UniqueString.internTbl.recover(fromChkpt);
            }
            FP64.Init(fpIndex);
    		
    		final RandomGenerator rng = new RandomGenerator();
            // Start checking:
            final int result;
			if (RunMode.SIMULATE.equals(runMode)) {
                // random simulation
                if (noSeed)
                {
                    seed = rng.nextLong();
                    rng.setSeed(seed);
                } else
                {
                    rng.setSeed(seed, aril);
    				RandomEnumerableValues.setSeed(seed);
                }
				printStartupBanner(EC.TLC_MODE_SIMU, getSimulationRuntime(seed));
				
				Simulator simulator;
				if (debugPort > 0) {
					assert TLCGlobals.getNumWorkers() == 1
							: "TLCDebugger does not support running with multiple workers.";
					final TLCDebugger instance = TLCDebugger.Factory.getInstance(suspend, halt);
					synchronized (instance) {
						tool = new DebugTool(mainFile, configFile, resolver, Tool.Mode.Simulation, instance.listen(debugPort));
					}
					simulator = new SingleThreadedSimulator(tool, metadir, traceFile, deadlock, traceDepth, 
	                        traceNum, traceActions, rng, seed, resolver);
				} else {
					tool = new FastTool(mainFile, configFile, resolver, Tool.Mode.Simulation);
					simulator = new Simulator(tool, metadir, traceFile, deadlock, traceDepth, 
	                        traceNum, traceActions, rng, seed, resolver, TLCGlobals.getNumWorkers());
				}
                TLCGlobals.simulator = simulator;
                result = simulator.simulate();
			} else { // RunMode.MODEL_CHECK
				if (noSeed) {
                    seed = rng.nextLong();
				}
				// Replace seed with tlc2.util.FP64.Polys[fpIndex]?
				// + No need to print seed in startup-banner for BFS and DFS
				// - Only 131 different seeds
				// RandomEnumerableValues.setSeed(tlc2.util.FP64.Polys[fpIndex]);
				RandomEnumerableValues.setSeed(seed);
            	
				// Print startup banner before SANY writes its output.
				printStartupBanner(isBFS() ? EC.TLC_MODE_MC : EC.TLC_MODE_MC_DFS, getModelCheckingRuntime(fpIndex, fpSetConfiguration));
				
            	// model checking
				if (debugPort > 0) {
					assert TLCGlobals.getNumWorkers() == 1 : "TLCDebugger does not support running with multiple workers.";
					final TLCDebugger instance = TLCDebugger.Factory.getInstance(suspend, halt);
					synchronized (instance) {
						tool = new DebugTool(mainFile, configFile, resolver, instance.listen(debugPort));
					}
				} else {
					tool = new FastTool(mainFile, configFile, resolver);
				}
                deadlock = deadlock && tool.getModelConfig().getCheckDeadlock();
                if (isBFS())
                {
					TLCGlobals.mainChecker = new ModelChecker(tool, metadir, stateWriter, deadlock, fromChkpt,
							FPSetFactory.getFPSetInitialized(fpSetConfiguration, metadir, new File(mainFile).getName()),
							startTime);
					modelCheckerMXWrapper = new ModelCheckerMXWrapper((ModelChecker) TLCGlobals.mainChecker, this);
					result = TLCGlobals.mainChecker.modelCheck();
                } else
                {
					TLCGlobals.mainChecker = new DFIDModelChecker(tool, metadir, stateWriter, deadlock, fromChkpt, startTime);
					result = TLCGlobals.mainChecker.modelCheck();
                }

            }
			return result;
        } catch (Throwable e)
        {
            if (e instanceof StackOverflowError)
            {
                System.gc();
                return MP.printError(EC.SYSTEM_STACK_OVERFLOW, e);
            } else if (e instanceof OutOfMemoryError)
            {
                System.gc();
                return MP.printError(EC.SYSTEM_OUT_OF_MEMORY, e);
            } else if (e instanceof TLCRuntimeException) {
            	return MP.printTLCRuntimeException((TLCRuntimeException) e);
            } else if (e instanceof RuntimeException) 
            {
                // SZ 29.07.2009 
                // printing the stack trace of the runtime exceptions
                return MP.printError(EC.GENERAL, e);
                // e.printStackTrace();
            } else
            {
                return MP.printError(EC.GENERAL, e);
            }
        } finally 
        {
        	if (tlc2.module.TLC.OUTPUT != null) {
        		try {
        			tlc2.module.TLC.OUTPUT.flush();
					tlc2.module.TLC.OUTPUT.close();
				} catch (IOException e) { }
        	}
			modelCheckerMXWrapper.unregister();
			// In tool mode print runtime in milliseconds, in non-tool mode print human
			// readable runtime (days, hours, minutes, ...).
			final long runtime = System.currentTimeMillis() - startTime;
			MP.printMessage(EC.TLC_FINISHED,
					// If TLC runs without -tool output it might still be useful to
					// report overall runtime in a machine-readable format (milliseconds)
					// instead of in a human-readable one.
					TLCGlobals.tool || Boolean.getBoolean(TLC.class.getName() + ".asMilliSeconds")
							? Long.toString(runtime) + "ms"
							: convertRuntimeToHumanReadable(runtime));

			// Generate trace exploration spec if error occurred.
			if (teSpec != null) {
				teSpec.generate(this.tool);
			}

			MP.unsubscribeRecorder(this.recorder);
			MP.flush();
        }
    }
    
	private static boolean isBFS() {
		return TLCGlobals.DFIDMax == -1;
	}

	public static Map<String, String> getSimulationRuntime(final long seed) {
		final Runtime runtime = Runtime.getRuntime();
		final long heapMemory = runtime.maxMemory() / 1024L / 1024L;
		
		final TLCRuntime tlcRuntime = TLCRuntime.getInstance();
		final long offHeapMemory = tlcRuntime.getNonHeapPhysicalMemory() / 1024L / 1024L;
		final long pid = tlcRuntime.pid();
		
		final Map<String, String> result = new LinkedHashMap<>();
		result.put("seed", String.valueOf(seed));
		result.put("workers", String.valueOf(TLCGlobals.getNumWorkers()));
		result.put("plural", TLCGlobals.getNumWorkers() == 1 ? "" : "s");
		result.put("cores", Integer.toString(runtime.availableProcessors()));
		result.put("osName", System.getProperty("os.name"));
		result.put("osVersion", System.getProperty("os.version"));
		result.put("osArch", System.getProperty("os.arch"));
		result.put("jvmVendor", System.getProperty("java.vendor"));
		result.put("jvmVersion", System.getProperty("java.version"));
		result.put("jvmArch", tlcRuntime.getArchitecture().name());
		result.put("jvmHeapMem", Long.toString(heapMemory));
		result.put("jvmOffHeapMem", Long.toString(offHeapMemory));
		result.put("jvmPid", pid == -1 ? "" : String.valueOf(pid));
		return result;
	}

	public static Map<String, String> getModelCheckingRuntime(final int fpIndex, final FPSetConfiguration fpSetConfig) {
		final Runtime runtime = Runtime.getRuntime();
		final long heapMemory = runtime.maxMemory() / 1024L / 1024L;
		
		final TLCRuntime tlcRuntime = TLCRuntime.getInstance();
		final long offHeapMemory = tlcRuntime.getNonHeapPhysicalMemory() / 1024L / 1024L;
		final long pid = tlcRuntime.pid();
		
		// TODO Better to use Class#getSimpleName provided we would have access to the
		// Class instance instead of just its name. However, loading the class here is
		// overkill and might interfere if other parts of TLC pull off class-loading
		// tricks.
		final String fpSetClassSimpleName = fpSetConfig.getImplementation()
				.substring(fpSetConfig.getImplementation().lastIndexOf(".") + 1);
		
		final String stateQueueClassSimpleName = ModelChecker.getStateQueueName();
		
		//  fpSetClassSimpleName and stateQueueClassSimpleName ignored in DFS mode.
		final Map<String, String> result = new LinkedHashMap<>();
		result.put("workers", String.valueOf(TLCGlobals.getNumWorkers()));
		result.put("plural", TLCGlobals.getNumWorkers() == 1 ? "" : "s");
		result.put("cores", Integer.toString(runtime.availableProcessors()));
		result.put("osName", System.getProperty("os.name"));
		result.put("osVersion", System.getProperty("os.version"));
		result.put("osArch", System.getProperty("os.arch"));
		result.put("jvmVendor", System.getProperty("java.vendor"));
		result.put("jvmVersion", System.getProperty("java.version"));
		result.put("jvmArch", tlcRuntime.getArchitecture().name());
		result.put("jvmHeapMem", Long.toString(heapMemory));
		result.put("jvmOffHeapMem", Long.toString(offHeapMemory));
		result.put("seed", Long.toString(RandomEnumerableValues.getSeed()));
		result.put("fpidx", Integer.toString(fpIndex));
		result.put("jvmPid", pid == -1 ? "" : String.valueOf(pid));
		result.put("fpset", fpSetClassSimpleName);
		result.put("queue", stateQueueClassSimpleName);
		return result;
	}
    
    /**
	 * @return The given milliseconds runtime converted into human readable form
	 *         with SI unit and insignificant parts stripped (when runtime is
	 *         days, nobody cares for minutes or seconds).
	 */
    public static String convertRuntimeToHumanReadable(long runtime) {
		SimpleDateFormat df = null;
		if (runtime > (60 * 60 * 24 * 1000L)) {
			df = new SimpleDateFormat("D'd' HH'h'");
			runtime -= 86400000L;
		} else if (runtime > (60 * 60 * 24 * 1000L)) {
			df = new SimpleDateFormat("D'd' HH'h'");
			runtime -= 86400000L;
		} else if (runtime > (60 * 60 * 1000L)) {
			df = new SimpleDateFormat("HH'h' mm'min'");
		} else if (runtime > (60 * 1000L)) {
			df = new SimpleDateFormat("mm'min' ss's'");
		} else {
			df = new SimpleDateFormat("ss's'");
		}
		df.setTimeZone(TimeZone.getTimeZone("UTC"));
		return df.format(runtime);
    }
    
	public List<File> getModuleFiles() {
    	final List<File> result = new ArrayList<File>();
    	
    	if (TLCGlobals.mainChecker instanceof ModelChecker) {
    		final ModelChecker mc = (ModelChecker) TLCGlobals.mainChecker;
    		result.addAll(mc.getModuleFiles(resolver));
    		if (ModelInJar.hasCfg()) {
    			result.add(ModelInJar.getCfg());
    		}
			// It might be desirable to include tlc.jfr - a flight recording aka profiling
			// at the JVM level here. This doesn't work though as the recording get created
			// after the termination of the JVM. A recording can also be several hundred
    		// MBs large.
    	}
        return result;
    }

    /**
     * Sets resolver for the file names
     * @param resolver a resolver for the names, if <code>null</code> is used, 
     * the standard resolver {@link SimpleFilenameToStream} is used
     */
    public void setResolver(FilenameToStream resolver)
    {
        this.resolver = resolver;
        ToolIO.setDefaultResolver(resolver);
    }
    
    public FilenameToStream getResolver() {
        return this.resolver;
    }
    
    public void setStateWriter(IStateWriter sw) {
    	this.stateWriter = sw;
    }

    /**
     * Print out an error message, with usage hint
     * @param msg, message to print
     * TODO remove this method and replace the calls
     */
    private void printErrorMsg(String msg)
    {
        printWelcome();
        MP.printError(EC.WRONG_COMMANDLINE_PARAMS_TLC, msg);
    }
    
    /**
     * Prints the welcome message once per instance
     */
    private void printWelcome()
    {
        if (!this.welcomePrinted) 
        {
            this.welcomePrinted = true;
            if (TLCGlobals.getRevision() == null) {
            	MP.printMessage(EC.TLC_VERSION, TLCGlobals.versionOfTLC);
            } else {
            	MP.printMessage(EC.TLC_VERSION, TLCGlobals.versionOfTLC + " (rev: " + TLCGlobals.getRevision() + ")");
            }
        }
    }
    
	private void printStartupBanner(final int mode, final Map<String, String> parameters) {
		MP.printMessage(mode, parameters.values().toArray(new String[parameters.size()]));
		
		final Map<String, String> udc = new LinkedHashMap<>();
		// First indicate the version (to make parsing forward compatible)
		udc.put("ver", TLCGlobals.getRevisionOrDev());

		// Simulation, DFS or BFS mode.
		udc.put("mode", mode2String(mode));
		
		parameters.remove("plural"); // damn hack!
		// "pid", "seed", and "fpidx" have no relevance for us.
		parameters.remove("jvmPid");
		parameters.remove("fpidx");
		parameters.remove("seed");
		udc.putAll(parameters);
		
		// True if TLC is run from within the Toolbox. Derive ide name from .tool too
		// unless set explicitly.  Eventually, we can probably remove the toolbox
		// parameter.
		udc.put("toolbox", Boolean.toString(TLCGlobals.tool));
		udc.put("ide", System.getProperty(TLC.class.getName() + ".ide", TLCGlobals.tool ? "toolbox" : "cli"));
		new ExecutionStatisticsCollector().collect(udc);
	}
	
	/**
	 * Gets the parent directory of the TLA file.
	 * @param tlaFilePath Path to a TLA file.
	 * @return Path to the parent directory of the TLA file.
	 */
	private static Path getTlaFileParentDir(String tlaFilePath) {
		if (null == tlaFilePath) {
			return Paths.get(".");
		}
		
		try {
			Path tlaDirPath = Paths.get(tlaFilePath).getParent();
			return null == tlaDirPath ? Paths.get(".") : tlaDirPath;
		} catch (InvalidPathException e) { return Paths.get("."); }
	}
	
	private static String mode2String(final int mode) {
		switch (mode) {
		case EC.TLC_MODE_MC:
			return "bfs";
		case EC.TLC_MODE_MC_DFS:
			return "dfs";
		case EC.TLC_MODE_SIMU:
			return "simulation";
		default:
			return "unknown";
		}
	}
    
    /**
     * 
     */
    private void printUsage()
    {
    	final List<List<UsageGenerator.Argument>> commandVariants = new ArrayList<>();
    	final List<UsageGenerator.Argument> sharedArguments = new ArrayList<>();
    	
    	// N.B. alphabetical ordering is not required by the UsageGenerator, but introduced here to more easily
    	//			find options when reading the code
    	sharedArguments.add(new UsageGenerator.Argument("-checkpoint", "minutes",
    													"interval between check point; defaults to 30",
    													true));
    	sharedArguments.add(new UsageGenerator.Argument("-cleanup", "clean up the states directory", true));
    	sharedArguments.add(new UsageGenerator.Argument("-config", "file",
    													"provide the configuration file; defaults to SPEC.cfg", true));
    	sharedArguments.add(new UsageGenerator.Argument("-continue",
    													"continue running even when an invariant is violated; default\n"
    														+ "behavior is to halt on first violation", true));
    	sharedArguments.add(new UsageGenerator.Argument("-coverage", "minutes",
														"interval between the collection of coverage information;\n"
    														+ "if not specified, no coverage will be collected", true));
    	sharedArguments.add(new UsageGenerator.Argument("-deadlock",
														"if specified DO NOT CHECK FOR DEADLOCK. Setting the flag is\n"
															+ "the same as setting CHECK_DEADLOCK to FALSE in config\n"
															+ "file. When -deadlock is specified, config entry is\n"
															+ "ignored; default behavior is to check for deadlocks",
														true));
    	sharedArguments.add(new UsageGenerator.Argument("-difftrace",
														"show only the differences between successive states when\n"
															+ "printing trace information; defaults to printing\n"
															+ "full state descriptions", true));
    	sharedArguments.add(new UsageGenerator.Argument("-debug",
														"print various debugging information - not for production use\n",
														true));
    	sharedArguments.add(new UsageGenerator.Argument("-dump", "file",
    													"dump all states into the specified file; this parameter takes\n"
    														+ "optional parameters for dot graph generation. Specifying\n"
    														+ "'dot' allows further options, comma delimited, of zero\n"
    														+ "or more of 'actionlabels', 'colorize', 'snapshot' to be\n"
    														+ "specified before the '.dot'-suffixed filename", true,
    													"dot actionlabels,colorize,snapshot"));
    	sharedArguments.add(new UsageGenerator.Argument("-fp", "N",
    													"use the Nth irreducible polynomial from the list stored\n"
    														+ "in the class FP64", true));
    	sharedArguments.add(new UsageGenerator.Argument("-fpbits", "num",
														"the number of MSB used by MultiFPSet to create nested\n"
    														+ "FPSets; defaults to 1", true));
    	sharedArguments.add(new UsageGenerator.Argument("-fpmem", "num",
														"a value in (0.0,1.0) representing the ratio of total\n"
															+ "physical memory to devote to storing the fingerprints\n"
															+ "of found states; defaults to 0.25", true));
    	sharedArguments.add(new UsageGenerator.Argument("-noGenerateSpecTE",
														"Whether to skip generating a trace exploration (TE) spec in\n"
															+ "the event of TLC finding a state or behavior that does\n"
															+ "not satisfy the invariants; TLC's default behavior is to\n"
															+ "generate this spec.", true));
		sharedArguments.add(new UsageGenerator.Argument("-teSpecOutDir", "some-dir-name",
														"Directory to which to output the TE spec if TLC generates\n"
															+ "an error trace. Can be a relative (to root spec dir)\n"
															+ "or absolute path. By default the TE spec is output\n"
															+ "to the same directory as the main spec.", true));
    	sharedArguments.add(new UsageGenerator.Argument("-gzip",
														"control if gzip is applied to value input/output streams;\n"
															+ "defaults to 'off'", true));
    	sharedArguments.add(new UsageGenerator.Argument("-h", "display these help instructions", true));
    	sharedArguments.add(new UsageGenerator.Argument("-maxSetSize", "num",
														"the size of the largest set which TLC will enumerate; defaults\n"
															+ "to 1000000 (10^6)", true));
    	sharedArguments.add(new UsageGenerator.Argument("-metadir", "path",
														"specify the directory in which to store metadata; defaults to\n"
															+ "SPEC-directory/states if not specified", true));
    	sharedArguments.add(new UsageGenerator.Argument("-nowarning",
														"disable all warnings; defaults to reporting warnings", true));
    	sharedArguments.add(new UsageGenerator.Argument("-recover", "id",
														"recover from the checkpoint with the specified id", true));
    	sharedArguments.add(new UsageGenerator.Argument("-terse",
														"do not expand values in Print statements; defaults to\n"
															+ "expanding values", true));
    	sharedArguments.add(new UsageGenerator.Argument("-tool",
														"run in 'tool' mode, surrounding output with message codes;\n"
															+ "if '-generateSpecTE' is specified, this is enabled\n"
															+ "automatically", true));
    	sharedArguments.add(new UsageGenerator.Argument("-userFile", "file",
														"an absolute path to a file in which to log user output (for\n"
    														+ "example, that which is produced by Print)", true));
    	sharedArguments.add(new UsageGenerator.Argument("-workers", "num",
														"the number of TLC worker threads; defaults to 1. Use 'auto'\n"
    														+ "to automatically select the number of threads based on the\n"
    														+ "number of available cores.", true));
    	sharedArguments.add(new UsageGenerator.Argument("-debugger", "nosuspend",
				"run simulation or model-checking in debug mode such that TLC's\n"
    				+ "state-space exploration can be temporarily halted and variables\n"
					+ "be inspected. The only debug front-end so far is the TLA+\n"
    				+ "VSCode extension, which has to be downloaded and configured\n"
					+ "separately, though other front-ends could be implemeted via the\n"
    				+ "debug-adapter-protocol.\n"
					+ "Specifying the optional parameter 'nosuspend' causes\n"
					+ "TLC to start state-space exploration without waiting for a\n"
					+ "debugger front-end to connect. Without 'nosuspend', TLC\n"
					+ "suspends state-space exploration before the first ASSUME is\n"
					+ "evaluated (but after constants are processed). With 'nohalt',\n"
					+ "TLC does not halt state-space exploration when an evaluation\n"
					+ "or runtime error is caught. Without 'nohalt', evaluation or\n"
					+ "runtime errors can be inspected in the debugger before TLC\n"
					+ "terminates. The optional parameter 'port=1274' makes the\n"
					+ "debugger listen on port 1274 instead of on the standard\n"
					+ "port 4712. Multiple optional parameters must be comma-separated.\n"
					+ "Specifying '-debugger' implies '-workers 1'."
					+ "", false,
				"nosuspend"));
  	
    	sharedArguments.add(new UsageGenerator.Argument("SPEC", null));
    	
    	
    	final List<UsageGenerator.Argument> modelCheckVariant = new ArrayList<>(sharedArguments);
    	modelCheckVariant.add(new UsageGenerator.Argument("-dfid", "num",
														  "run the model check in depth-first iterative deepening\n"
    														+ "starting with an initial depth of 'num'", true));
    	modelCheckVariant.add(new UsageGenerator.Argument("-view",
														  "apply VIEW (if provided) when printing out states", true));
    	commandVariants.add(modelCheckVariant);
    	
    	
    	final List<UsageGenerator.Argument> simulateVariant = new ArrayList<>(sharedArguments);
    	simulateVariant.add(new UsageGenerator.Argument("-depth", "num",
														"specifies the depth of random simulation; defaults to 100",
														true));
    	simulateVariant.add(new UsageGenerator.Argument("-seed", "num",
														"provide the seed for random simulation; defaults to a\n"
    														+ "random long pulled from a pseudo-RNG", true));
    	simulateVariant.add(new UsageGenerator.Argument("-aril", "num",
														"adjust the seed for random simulation; defaults to 0", true));
    	simulateVariant.add(new UsageGenerator.Argument("-simulate", null,
													  	"run in simulation mode; optional parameters may be specified\n"
	    													+ "comma delimited: 'num=X' where X is the maximum number of\n"
	    													+ "total traces to generate and/or 'file=Y' where Y is the\n"
	    													+ "absolute-pathed prefix for trace file modules to be written\n"
	    													+ "by the simulation workers; for example Y='/a/b/c/tr' would\n"
	    													+ "produce, e.g, '/a/b/c/tr_1_15'", false,
	    												"file=X,num=Y"));
    	// implies workers 1
    	// bfs and simulation only (no iddfs)
    	commandVariants.add(simulateVariant);

    	
    	final List<String> tips = new ArrayList<String>();
    	tips.add("When using the  '-generateSpecTE' you can version the generated specification by doing:\n\t"
    				+ "./tla2tools.jar -generateSpecTE MySpec.tla && NAME=\"SpecTE-$(date +%s)\" && sed -e \"s/MODULE"
    				+ " SpecTE/MODULE $NAME/g\" SpecTE.tla > $NAME.tla");
    	tips.add("If, while checking a SpecTE created via '-generateSpecTE', you get an error message concerning\n"
    				+ "CONSTANT declaration and you've previous used 'integers' as model values, rename your\n"
    				+ "model values to start with a non-numeral and rerun the model check to generate a new SpecTE.");
    	tips.add("If, while checking a SpecTE created via '-generateSpecTE', you get a warning concerning\n"
					+ "duplicate operator definitions, this is likely due to the 'monolith' specification\n"
					+ "creation. Try re-running TLC adding the 'nomonolith' option to the '-generateSpecTE'\n"
					+ "parameter.");
    	
    	UsageGenerator.displayUsage(ToolIO.out, "TLC", TLCGlobals.versionOfTLC,
    								"provides model checking and simulation of TLA+ specifications",
    								Messages.getString("TLCDescription"),
    								commandVariants, tips, ' ');
    }

    FPSetConfiguration getFPSetConfiguration() {
    	return fpSetConfiguration;
    }
    
    public RunMode getRunMode() {
    	return runMode;
    }

    public String getMainFile() {
        return mainFile;
    }
    
    public long getStartTime() {
    	return startTime;
    }

	public String getModelName() {
		return System.getProperty(MailSender.MODEL_NAME, this.mainFile);
	}
	
	public String getSpecName() {
		return System.getProperty(MailSender.SPEC_NAME, this.mainFile);
	}
}
