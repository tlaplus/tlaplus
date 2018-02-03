// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Thu 10 April 2008 at 14:31:23 PST by lamport 
//      modified on Wed Dec  5 22:37:20 PST 2001 by yuanyu 

package tlc2;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;
import java.util.TimeZone;

import model.InJarFilenameToStream;
import model.ModelInJar;
import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.AbstractChecker;
import tlc2.tool.Cancelable;
import tlc2.tool.DFIDModelChecker;
import tlc2.tool.ModelChecker;
import tlc2.tool.Simulator;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.management.ModelCheckerMXWrapper;
import tlc2.tool.management.TLCStandardMBean;
import tlc2.util.FP64;
import tlc2.util.RandomGenerator;
import tlc2.value.Value;
import util.DebugPrinter;
import util.FileUtil;
import util.FilenameToStream;
import util.MailSender;
import util.SimpleFilenameToStream;
import util.TLCRuntime;
import util.ToolIO;
import util.UniqueString;

/**
 * Main TLC starter class
 * @author Yuan Yu
 * @author Leslie Lamport
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLC
{
    
    private static boolean MODEL_PART_OF_JAR = false;

    // SZ Feb 20, 2009: the class has been 
    // transformed from static to dynamic
    private boolean isSimulate; 
    private boolean cleanup;
    private boolean deadlock;

    private boolean noSeed;
    private long seed;
    private long aril;

    private String mainFile;
    private String configFile;
    private String dumpFile;
    /**
	 * If true, the dumpFile will be written in dot format to be processed by
	 * GraphViz.
	 * <p>
	 * Contrary to plain -dump, -dot will also write out transitions from state
	 * s to s' if s' is already known. Thus, the resulting graph shows all
	 * successors of s instead of just s's unexplored ones.
	 * <p>
	 * Off/False by default.
	 */
    private boolean asDot;
    private boolean colorize = false;
    private boolean actionLabels = false;

    private String fromChkpt;

    private int fpIndex;
    /**
     * The number of traces/behaviors to generate in simulation mode
     */
    public static long traceNum = Long.MAX_VALUE;
    private int traceDepth;
    private FilenameToStream resolver;
    private SpecObj specObj;

    // flag if the welcome message is already printed
    private boolean welcomePrinted;
    
    // handle to the cancellable instance (MC or Simulator)
    private Cancelable instance;

    private FPSetConfiguration fpSetConfiguration;
    
    /**
     * Initialization
     */
    public TLC()
    {
        welcomePrinted = false;
        
        isSimulate = false; // Default to model checking
        cleanup = false;
        deadlock = true;
        
        noSeed = true;
        seed = 0;
        aril = 0;
        
        mainFile = null;
        configFile = null;
        dumpFile = null;
        asDot = false;
        fromChkpt = null;
        resolver = null;

        fpIndex = 0;
        traceDepth = 100;
        
        // instance is not set
        instance = null;

        fpSetConfiguration = new FPSetConfiguration();
    }

    /*
     * This TLA checker (TLC) provides the following functionalities:
     *  1. Simulation of TLA+ specs: java tlc2.TLC -simulate spec[.tla]
     *  2. Model checking of TLA+ specs: java tlc2.TLC [-modelcheck] spec[.tla]
     *
     * The command line also provides the following options:
     *  o -config file: provide the config file.
     *    Defaults to spec.cfg if not provided
     *  o -deadlock: do not check for deadlock.
     *    Defaults to checking deadlock if not specified
     *  o -depth num: specify the depth of random simulation 
     *    Defaults to 100 if not specified
     *  o -seed num: provide the seed for random simulation
     *    Defaults to a random seed if not specified
     *  o -aril num: Adjust the seed for random simulation
     *    Defaults to 0 if not specified
     *  o -recover path: recover from the checkpoint at path
     *    Defaults to scratch run if not specified
     *  o -bound: The upper limit for sets effectively limiting the number of init states
     *    (@see Bug #264 in general/bugzilla/index.html)
     *    Defaults to 1000000 if not specified
     *  o -metadir path: store metadata in the directory at path
     *    Defaults to specdir/states if not specified
	 *  o -userFile file: A full qualified/absolute path to a file to log user
	 *    output (Print/PrintT/...) to
     *  o -workers num: the number of TLC worker threads
     *    Defaults to 1
     *  o -dfid num: use depth-first iterative deepening with initial depth num
     *  o -cleanup: clean up the states directory
     *  o -dump [dot] file: dump all the states into file. If "dot" as sub-parameter
     *                      is given, the output will be in dot notation.
     *  o -difftrace: when printing trace, show only
     *                the differences between successive states
     *    Defaults to printing full state descriptions if not specified
     *    (Added by Rajeev Joshi)
     *  o -terse: do not expand values in Print statement
     *    Defaults to expand value if not specified
     *  o -coverage minutes: collect coverage information on the spec,
     *                       print out the information every minutes.
     *    Defaults to no coverage if not specified
     *  o -continue: continue running even when invariant is violated
     *    Defaults to stop at the first violation if not specified
     *  o -lncheck: Check liveness properties at different times
     *    of model checking.
     *    Defaults to false increasing the overall model checking time.
     *  o -nowarning: disable all the warnings
     *    Defaults to report warnings if not specified
     *  o -fp num: use the num'th irreducible polynomial from the list
     *    stored in the class FP64.
     *  o -view: apply VIEW (if provided) when printing out states.
     *  o -gzip: control if gzip is applied to value input/output stream.
     *    Defaults to use gzip.
     *  o -debug: debbuging information (non-production use)
     *  o -tool: tool mode (put output codes on console)
     *  o -checkpoint num: interval for check pointing (in minutes)
     *     Defaults to 30
     *  o -fpmem num: the number of megabytes of memory used to store
     *                the fingerprints of found states.
     *  Defaults to 1/4 physical memory.  (Added 6 Apr 2010 by Yuan Yu.)
     *  o -fpbits num: the number of msb used by MultiFPSet to create nested FPSets.
     *  Defaults to 1
     *  o -maxSetSize num: the size of the largest set TLC will enumerate.
     *                     default: 1000000
     *   
     */
    public static void main(String[] args) throws Exception
    {
        TLC tlc = new TLC();

        // handle parameters
        if (tlc.handleParameters(args))
        {
        	final MailSender ms = new MailSender();
        	if (MODEL_PART_OF_JAR) {
        		tlc.setResolver(new InJarFilenameToStream(ModelInJar.PATH));
        	} else {
        		tlc.setResolver(new SimpleFilenameToStream());
        	}
        	ms.setModelName(tlc.getModelName());
        	ms.setSpecName(tlc.getSpecName());

            // call the actual processing method
            tlc.process();

            // Send logged output by email
            boolean success = ms.send(tlc.getModuleFiles());
            
			// In case sending the mail has failed, we treat this as an error.
			// This is needed when TLC runs on another host and email is
			// the only means for the user to get access to the model checking
			// results. 
			// With distributed TLC and CloudDistributedTLCJob in particular,
			// the cloud node is immediately turned off once the TLC process has
			// finished. If we were to shutdown the node even when sending out 
            // the email has failed, the result would be lost.
			if (!success) {
				System.exit(1);
			}
        }
        // terminate
        System.exit(0);
    }

    /**
     * This method handles parameter arguments and prepares the actual call
     * <strong>Note:</strong> This method set ups the static TLCGlobals variables
     * @return status of parsing: true iff parameter check was ok, false otherwise
     */
    // SZ Feb 23, 2009: added return status to indicate the error in parsing
    @SuppressWarnings("deprecation")
	public boolean handleParameters(String[] args)
    {
        // SZ Feb 20, 2009: extracted this method to separate the 
        // parameter handling from the actual processing
        int index = 0;
		while (index < args.length)
        {
            if (args[index].equals("-simulate"))
            {
                isSimulate = true;
                index++;
            } else if (args[index].equals("-modelcheck"))
            {
                isSimulate = false;
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
                Value.expand = false;
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
            } else if (args[index].equals("-tool"))
            {
                index++;
                TLCGlobals.tool = true;
            } else if (args[index].equals("-help"))
            {
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
                    int len = configFile.length();
                    if (configFile.startsWith(".cfg", len - 4))
                    {
                        configFile = configFile.substring(0, len - 4);
                    }
                    index++;
                } else
                {
                    printErrorMsg("Error: expect a file name for -config option.");
                    return false;
                }
            } else if (args[index].equals("-dump"))
            {
            	String suffix = ".dump";
            	
                index++;
                if (index < args.length && args[index].equals("dot"))
                {
                    asDot = true;
                    suffix = ".dot";
                    index++;
                }
                if (index < args.length)
                {
                    dumpFile = args[index];
					// Require a $suffix file extension unless already given. It
					// is not clear why this is enforced.
                    int len = dumpFile.length();
                    if (!(dumpFile.startsWith(suffix, len - suffix.length())))
                    {
                        dumpFile = dumpFile + suffix;
                    }
                    index++;
                } else
                {
                    printErrorMsg("Error: A file name for dumping states required.");
                    return false;
                }
            } else if (args[index].equals("-colorize")) {
            		// Colorize state transition edges in the DOT state graph. Each action
            		// gets a unique color.
                colorize = true;
                index++;

            } else if (args[index].equals("-actionLabels")) {
            		// Label transition edges in the state graph with the name of the
            		// associated action. Can potentially add a large amount of visual clutter for
            		// large graphs with many actions.
                actionLabels = true;
                index++;
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
						// Most problems will only show we TLC eventually tries
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
                        int num = Integer.parseInt(args[index]);
                        if (num < 1)
                        {
                            printErrorMsg("Error: at least one worker required.");
                            return false;
                        }
                        TLCGlobals.setNumWorkers(num);
                        index++;
                    } catch (Exception e)
                    {
                        printErrorMsg("Error: worker number required. But encountered " + args[index]);
                        return false;
                    }
                } else
                {
                    printErrorMsg("Error: expect an integer for -workers option.");
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
                        printErrorMsg("Errorexpect a nonnegative integer for -dfid option. " + "But encountered "
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
                    printErrorMsg("Error: expect an integer for -workers option.");
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
                int len = mainFile.length();
                if (mainFile.startsWith(".tla", len - 4))
                {
                    mainFile = mainFile.substring(0, len - 4);
                }
            }
        }
        
        if (mainFile == null)
        {
			// command line omitted name of spec file, take this as an
			// indicator to check the in-jar model/ folder for a spec.
			// If a spec is found, use it instead.
			if (ModelInJar.hasModel()) {
				MODEL_PART_OF_JAR = true;
				ModelInJar.loadProperties();
				TLCGlobals.tool = true; // always run in Tool mode (to parse output by Toolbox later)
				TLCGlobals.chkptDuration = 0; // never use checkpoints with distributed TLC (highly inefficient)
				mainFile = "MC";
			} else {
				printErrorMsg("Error: Missing input TLA+ module.");
				return false;
			}
        }
        if (configFile == null)
        {
            configFile = mainFile;
        }
        
        if (TLCGlobals.debug) 
        {
		StringBuffer buffer = new StringBuffer("TLC arguments:");
		for (int i=0; i < args.length; i++)
		{
		    buffer.append(args[i]);
		    if (i < args.length - 1) 
		    {
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
     * The processing method
     */
    public void process()
    {
    	long startTime = System.currentTimeMillis();
    	
        ToolIO.cleanToolObjects(TLCGlobals.ToolId);
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
            if (cleanup && fromChkpt == null)
            {
                // clean up the states directory only when not recovering
                FileUtil.deleteDir(TLCGlobals.metaRoot, true);
            }
            FP64.Init(fpIndex);

            
    		final TLCRuntime tlcRuntime = TLCRuntime.getInstance();
    		final long offHeapMemory = tlcRuntime.getNonHeapPhysicalMemory() / 1024L / 1024L;
    		final String arch = tlcRuntime.getArchitecture().name();
    		
    		final Runtime runtime = Runtime.getRuntime();
    		final long heapMemory = runtime.maxMemory() / 1024L / 1024L;
    		final String cores = Integer.toString(runtime.availableProcessors());

    		final String vendor = System.getProperty("java.vendor");
    		final String version = System.getProperty("java.version");

    		final String osName = System.getProperty("os.name");
    		final String osVersion = System.getProperty("os.version");
    		final String osArch = System.getProperty("os.arch");
    		
            // Start checking:
            if (isSimulate)
            {
                // random simulation
                RandomGenerator rng = new RandomGenerator();
                if (noSeed)
                {
                    seed = rng.nextLong();
                    rng.setSeed(seed);
                } else
                {
                    rng.setSeed(seed, aril);
                }
				MP.printMessage(EC.TLC_MODE_SIMU,
						new String[] { String.valueOf(seed), String.valueOf(TLCGlobals.getNumWorkers()),
								TLCGlobals.getNumWorkers() == 1 ? "" : "s", cores, osName, osVersion, osArch, vendor,
								version, arch, Long.toString(heapMemory), Long.toString(offHeapMemory) });
                Simulator simulator = new Simulator(mainFile, configFile, null, deadlock, traceDepth, 
                        traceNum, rng, seed, true, resolver, specObj);
                TLCGlobals.simulator = simulator;
// The following statement moved to Spec.processSpec by LL on 10 March 2011               
//                MP.printMessage(EC.TLC_STARTING);
                instance = simulator;
                simulator.simulate();
            } else
            {
            	final String[] parameters = new String[] { String.valueOf(TLCGlobals.getNumWorkers()),
            			TLCGlobals.getNumWorkers() == 1 ? "" : "s", cores, osName, osVersion, osArch, vendor,
            					version, arch, Long.toString(heapMemory), Long.toString(offHeapMemory) };

            	// model checking
        		AbstractChecker mc = null;
                if (TLCGlobals.DFIDMax == -1)
                {
					MP.printMessage(EC.TLC_MODE_MC, parameters);
                    mc = new ModelChecker(mainFile, configFile, dumpFile, asDot, colorize, actionLabels, deadlock, fromChkpt, resolver, specObj, fpSetConfiguration);
                    modelCheckerMXWrapper = new ModelCheckerMXWrapper((ModelChecker) mc, this);
                } else
                {
					MP.printMessage(EC.TLC_MODE_MC_DFS, parameters);
                    mc = new DFIDModelChecker(mainFile, configFile, dumpFile, asDot, colorize, actionLabels, deadlock, fromChkpt, true, resolver, specObj);
                }
                TLCGlobals.mainChecker = mc;
// The following statement moved to Spec.processSpec by LL on 10 March 2011               
//                MP.printMessage(EC.TLC_STARTING);
                instance = mc;
                mc.modelCheck();
                
            }
        } catch (Throwable e)
        {
            if (e instanceof StackOverflowError)
            {
                System.gc();
                MP.printError(EC.SYSTEM_STACK_OVERFLOW, e);
            } else if (e instanceof OutOfMemoryError)
            {
                System.gc();
                MP.printError(EC.SYSTEM_OUT_OF_MEMORY, e);
            } else if (e instanceof RuntimeException) 
            {
                // SZ 29.07.2009 
                // printing the stack trace of the runtime exceptions
                MP.printError(EC.GENERAL, e);
                // e.printStackTrace();
            } else
            {
                MP.printError(EC.GENERAL, e);
            }
        } finally 
        {
        	if (tlc2.module.TLC.OUTPUT != null) {
        		try {
        			tlc2.module.TLC.OUTPUT.flush();
					tlc2.module.TLC.OUTPUT.close();
				} catch (IOException e) {
				}
        	}
			modelCheckerMXWrapper.unregister();
			// In tool mode print runtime in milliseconds, in non-tool mode print human
			// readable runtime (days, hours, minutes, ...).
			final long runtime = System.currentTimeMillis() - startTime;
			MP.printMessage(EC.TLC_FINISHED,
					TLCGlobals.tool ? Long.toString(runtime) + "ms" : convertRuntimeToHumanReadable(runtime));
			MP.flush();
        }
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
    	
    	if (instance instanceof ModelChecker) {
    		ModelChecker mc = (ModelChecker) instance;
			final Enumeration<ParseUnit> parseUnitContext = mc.specObj.parseUnitContext
					.elements();
    		while (parseUnitContext.hasMoreElements()) {
    			ParseUnit pu = (ParseUnit) parseUnitContext.nextElement();
				File resolve = resolver.resolve(pu.getFileName(), false);
				result.add(resolve);
    		}
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

    /**
     * Set external specification object
     * @param specObj spec object created external SANY run
     */
    public void setSpecObject(SpecObj specObj) 
    {
        this.specObj = specObj;
    }

    /**
     * Delegate cancellation request to the instance
     * @param flag
     */
    public void setCanceledFlag(boolean flag)
    {
        if (this.instance != null) 
        {
            this.instance.setCancelFlag(flag);
            DebugPrinter.print("Cancel flag set to " + flag);
        }
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
    
    /**
     * 
     */
    private void printUsage()
    {
        printWelcome();
        MP.printMessage(EC.TLC_USAGE);
    }

    FPSetConfiguration getFPSetConfiguration() {
    	return fpSetConfiguration;
    }

	public String getModelName() {
		return System.getProperty(MailSender.MODEL_NAME, this.mainFile);
	}
	
	public String getSpecName() {
		return System.getProperty(MailSender.SPEC_NAME, this.mainFile);
	}
}
