// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Thu 10 April 2008 at 14:31:23 PST by lamport 
//      modified on Wed Dec  5 22:37:20 PST 2001 by yuanyu 

package tlc2;

import java.io.BufferedOutputStream;
import java.io.BufferedWriter;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.io.PrintStream;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TimeZone;
import java.util.concurrent.Phaser;

import model.InJarFilenameToStream;
import model.ModelInJar;
import tlc2.input.MCOutputPipeConsumer;
import tlc2.input.MCParser;
import tlc2.input.MCParserResults;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.output.Messages;
import tlc2.output.TLAMonolithCreator;
import tlc2.output.TeeOutputStream;
import tlc2.tool.DFIDModelChecker;
import tlc2.tool.ITool;
import tlc2.tool.ModelChecker;
import tlc2.tool.Simulator;
import tlc2.tool.TLCState;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.FPSetFactory;
import tlc2.tool.impl.FastTool;
import tlc2.tool.impl.ModelConfig;
import tlc2.tool.impl.SpecProcessor;
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
import util.Either;

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
    private static boolean MODEL_PART_OF_JAR = false;
    
    public enum RunMode {
    	MODEL_CHECK, SIMULATE;
    }
    

    // SZ Feb 20, 2009: the class has been 
    // transformed from static to dynamic

    private RunMode runMode;
    private boolean cleanup;
    private boolean checkDeadlock;

    private boolean generateErrorTraceSpec;
    private boolean requireMonolithicErrorTraceSpec;

    private boolean noSeed;
    private long seed;
    private long aril;
    
	private long startTime;

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

    private String fromChkpt;

    private int fpIndex;
    /**
     * The number of traces/behaviors to generate in simulation mode
     */
    private static long traceNum = Long.MAX_VALUE;
    private String traceFile = null;
    private int traceDepth;
    private FilenameToStream resolver;
    
    private String dumpFile = null;
	private boolean asDot = false;
	private boolean colorize = false;
	private boolean actionLabels = false;
	private boolean snapshot = false;
		
	private String userFile = null;

    // flag if the welcome message is already printed
    private boolean welcomePrinted;
    
    private FPSetConfiguration fpSetConfiguration;
    
    private volatile ITool tool;
    private final Phaser waitingOnGenerationCompletion;
    
    /**
     * Initialization
     */
	public TLC() {
        welcomePrinted = false;
        
        runMode = RunMode.MODEL_CHECK;
        cleanup = false;
        checkDeadlock = true;
        this.generateErrorTraceSpec = false;
        this.requireMonolithicErrorTraceSpec = false;
        
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
        
        waitingOnGenerationCompletion = new Phaser();
        waitingOnGenerationCompletion.register();
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
        
        if (!tlc.initialize(args))
        {
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
	 * Parses command line parameters and sets up class & global variables
	 * @param args The command line parameters to parse
	 * @return True IFF there were no parsing or input validation errors
	 */
	public boolean handleParameters(String[] args)
    {
		// Parse command line options
		CommandLineOptions.ParseResult parseResult = CommandLineOptions.parse(args);

		if (!parseResult.success)
		{
			this.printErrorMsg(parseResult.errorMessage.get());
			return false;
		}
		
		if (parseResult.helpRequest)
		{
			this.printUsage();
			return false;
		}
		
		// Validate command line options
		CommandLineOptions options = parseResult.options.get();
		Either<CommandLineOptions.FailedValidationResult,
				CommandLineOptions.SuccessfulValidationResult> validationResult =
					CommandLineOptions.validate(options);
		return validationResult.map(
				(failure) -> {
					this.printErrorMsg(failure.errorMessage);
					return false;
				},
				(success) -> {
					CommandLineOptions.transform(options);
					this.setClassVariables(options);
					this.setGlobalVariables(options);
					return true;
				});
    }
	
	@SuppressWarnings("deprecation")	// we're emitting a warning to the user, but still accepting fpmem values > 1
	private void setClassVariables(CommandLineOptions options)
	{
		if (options.simulationModeFlag)
		{
			this.runMode = RunMode.SIMULATE;
			options.simulationBehaviorCountLimit.ifPresent(value -> {
				TLC.traceNum = value;
			});
			options.simulationTraceFile.ifPresent(value -> {
				this.traceFile = value;
			});
		}
		
		if (options.doNotCheckDeadlockFlag)
		{
			this.checkDeadlock = false;
		}
		
		if (options.cleanStatesDirectoryFlag)
		{
			this.cleanup = true;
		}
		
		if (options.generateErrorTraceSpecFlag)
		{
			TLCGlobals.tool = true;
			this.generateErrorTraceSpec = true;
			if (options.noMonolithErrorTraceSpecFlag)
			{
				this.requireMonolithicErrorTraceSpec = false;
			}
		}

		options.configurationFilePath.ifPresent(value -> {
			this.configFile = value;
		});
		
		options.dumpFilePath.ifPresent(value -> {
			this.dumpFile = value;
			options.dumpFileOptions.ifPresent(dumpOptions ->
			{
				this.asDot = true;
				this.colorize = dumpOptions.colorize;
				this.actionLabels = dumpOptions.actionLabels;
				this.snapshot = dumpOptions.snapshot;
			});
		});

		options.simulationTraceDepthLimit.ifPresent(value -> {
			this.traceDepth = value;
		});
		
		options.seed.ifPresent(value -> {
			this.noSeed = false;
			this.seed = value;
		});
		
		options.aril.ifPresent(value -> {
			this.aril = value;
		});

		options.recoveryId.ifPresent(value -> {
			this.fromChkpt = value;
		});
		
		options.userOutputFilePath.ifPresent(value -> {
			this.userFile = value;
		});
		
		options.fingerprintFunctionIndex.ifPresent(value -> {
			this.fpIndex = value;
		});
		
		options.fingerprintSetMemoryUsePercentage.ifPresent(value -> {
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
			if (value > 1)
			{
				// For legacy reasons we allow users to set the
				// absolute amount of memory. If this is the case,
				// we know the user intends to allocate all 100% of
				// the absolute memory to the fpset.
				ToolIO.out.println(
						"Using -fpmem with an abolute memory value has been deprecated. " +
						"Please allocate memory for the TLC process via the JVM mechanisms " +
						"and use -fpmem to set the fraction to be used for fingerprint storage.");
				this.fpSetConfiguration.setMemory((long)value.doubleValue());
				this.fpSetConfiguration.setRatio(1.0d);
				
			} else
			{
				this.fpSetConfiguration.setRatio(value);
			}
		});
		
		options.fingerprintBits.ifPresent(value -> {
			this.fpSetConfiguration.setFpBits(value);
		});
		
		options.mainSpecFilePath.ifPresent(value -> {
			this.mainFile = value;
		});
	}
	
	/**
	 * Applies the command line options to various variables.
	 * @param options The parsed command line options.
	 */
	private void setGlobalVariables(CommandLineOptions options)
	{
		if (options.onlyPrintStateTraceDiffsFlag)
		{
			TLCGlobals.printDiffsOnly = true;
		}
		
		if (options.doNotPrintWarningsFlag)
		{
			TLCGlobals.warn = false;
		}
		
		if (options.useGZipFlag)
		{
			TLCGlobals.useGZIP = true;
		}
		
		if (options.terseOutputFlag)
		{
			TLCGlobals.expand = false;
		}
		
		if (options.continueAfterInvariantViolationFlag)
		{
			TLCGlobals.continuation = true;
		}
		
		if (options.useViewFlag)
		{
			TLCGlobals.useView = true;
		}
		
		if (options.debugFlag)
		{
			TLCGlobals.debug = true;
		}
		
		if (options.useToolOutputFormatFlag)
		{
			TLCGlobals.tool = true;
		}
		
		options.livenessCheck.ifPresent(value -> {
			TLCGlobals.lnCheck = value;
		});
		
		options.coverageIntervalInMinutes.ifPresent(value -> {
			// Convert minutes to milliseconds
			TLCGlobals.coverageInterval = value * 60 * 1000;
		});
		
		options.checkpointIntervalInMinutes.ifPresent(value -> {
			// Convert minutes to milliseconds
			TLCGlobals.chkptDuration = value * 60 * 1000;
		});
		
		options.maxSetSize.ifPresent(value -> {
			TLCGlobals.setBound = value;
		});
		
		options.metadataDirectoryPath.ifPresent(value -> {
			TLCGlobals.metaDir = value;
		});
		
		options.tlcWorkerThreadOptions.ifPresent(either -> {
			either.ifPresent(auto -> {
				// TODO: validate this call result
				int workerCount = Runtime.getRuntime().availableProcessors();
				TLCGlobals.setNumWorkers(workerCount);
			}, manual -> {
				TLCGlobals.setNumWorkers(manual.workerThreadCount);
			});
		});
		
		options.dfidStartingDepth.ifPresent(value -> {
			TLCGlobals.DFIDMax = value;
		});
	}
	
	public boolean initialize(String[] args)
	{
        startTime = System.currentTimeMillis();

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
		
		if (this.userFile != null) {
			try
			{
				// Most problems will only show when TLC eventually tries
				// to write to the file.
				tlc2.module.TLC.OUTPUT = new BufferedWriter(new FileWriter(new File(this.userFile)));
			} catch (IOException e) {
				printErrorMsg("Error: Failed to create user output log file.");
				return false;
			}
		}

		if (this.generateErrorTraceSpec & waitingOnGenerationCompletion.getRegisteredParties() <= 1)
		{
			// Don't start the shebang below twice, if a user accidentally passed
			// '-generateSpecTE' twice.
			
			// This reads the output (ToolIO.out) on stdout of all other TLC threads. The
			// output is parsed to reconstruct the error trace, from which the code below
			// generates the SpecTE file. It might seem as if it would have been easier to
			// reuse the MPRecorder to collect the output that's written to ToolIO, but this
			// would work with two TLC processes where the first runs model-checking and
			// pipes its output to the second.
			try {
				final ByteArrayOutputStream temporaryMCOutputStream = new ByteArrayOutputStream();
				final BufferedOutputStream bos = new BufferedOutputStream(temporaryMCOutputStream);
				final PipedInputStream pis = new PipedInputStream();
				final TeeOutputStream tos1 = new TeeOutputStream(bos, new PipedOutputStream(pis));
				final TeeOutputStream tos2 = new TeeOutputStream(ToolIO.out, tos1);
				ToolIO.out = new PrintStream(tos2);
				final MCOutputPipeConsumer mcOutputConsumer = new MCOutputPipeConsumer(pis, null);
				
				// Note, this runnable's thread will not finish consuming output until just
				// 	before the app exits and we will use the output consumer in the TLC main
				//	thread while it is still consuming (but at a point where the model checking
				//	itself has finished and so the consumer is as populated as we need it to be
				//	- but prior to the output consumer encountering the EC.TLC_FINISHED message.)
				final Runnable r = () -> {
					boolean haveClosedOutputStream = false;
					try {
						waitingOnGenerationCompletion.register();
						mcOutputConsumer.consumeOutput();
						
						bos.flush();
						temporaryMCOutputStream.close();
						haveClosedOutputStream = true;
						
						if ((mcOutputConsumer != null) && (mcOutputConsumer.getError() != null)) {
							// We need not synchronize the access to tool (which might appear racy), because
							// the consumeOutput above will block until TLC's finish message, which is written
							// *after* tool has been created.
							final SpecProcessor sp = tool.getSpecProcessor();
							final ModelConfig mc = tool.getModelConfig();
							final File sourceDirectory = mcOutputConsumer.getSourceDirectory();
							final String originalSpecName = mcOutputConsumer.getSpecName();
							
							final MCParserResults mcParserResults = MCParser.generateResultsFromProcessorAndConfig(sp, mc);

							// Write the files SpecTE.tla and SpecTE.cfg
							// At this point SpecTE.cfg contains the content of MC.cfg.
							// SpecTE.tla contains the newly generated SpecTE and the content of MC.tla.
							// See https://github.com/tlaplus/tlaplus/issues/475 for why copying MC.tla/MC.cfg is wrong.
							final File[] files = TraceExplorer.writeSpecTEFiles(sourceDirectory, originalSpecName,
									TLCState.Empty.getVarsAsStrings(), mcParserResults, mcOutputConsumer.getError());
							
							// This rewrites SpecTE.tla in an attempt to create a monolith spec.
							// See https://github.com/tlaplus/tlaplus/issues/479 and
							// https://github.com/tlaplus/tlaplus/issues/479 why this is broken.
							if (this.requireMonolithicErrorTraceSpec) {
								final List<File> extendedModules = mcOutputConsumer.getExtendedModuleLocations();
								final TLAMonolithCreator monolithCreator
									= new TLAMonolithCreator(TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME,
															 mcOutputConsumer.getSourceDirectory(),
															 extendedModules,
															 mcParserResults.getAllExtendedModules(),
															 mcParserResults.getAllInstantiatedModules());
								// Beware, this internally creates a temp file and re-reads SpecTE.tla from disk again. 
								monolithCreator.copy();
							}
							
							// *Append* TLC's stdout/stderr output to final SpecTE.tla. The content of SpecTE.tla
							// is now MonolithMC, MonolithSpecTE, stdout/stderr. Most users won't care for
							// stderr/stdout and want to look at SpecTE. Thus, SpecTE is at the top.
							final FileOutputStream fos = new FileOutputStream(files[0], true);
							FileUtil.copyStream(new ByteArrayInputStream(temporaryMCOutputStream.toByteArray()), fos);
							
							fos.close();
						}
						
					} catch (final Exception e) {
						MP.printMessage(EC.GENERAL,
										"A model checking error occurred while parsing tool output; the execution "
												+ "ended before the potential "
												+ TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME
												+ " generation stage.");
					} finally {
						if (!haveClosedOutputStream) {
							try {
								bos.flush();
								temporaryMCOutputStream.close();
							} catch (final Exception e) { }
						}
						// Signal the main method to continue to termination.
							waitingOnGenerationCompletion.arriveAndDeregister();
						}
					};
					new Thread(r).start();

				} catch (final IOException ioe) {
					printErrorMsg("Failed to set up piped output consumers; no potential "
										+ TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + " will be generated: "
										+ ioe.getMessage());
				}
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
				
				Simulator simulator = new Simulator(mainFile, configFile, traceFile, checkDeadlock, traceDepth, 
                        traceNum, rng, seed, resolver, TLCGlobals.getNumWorkers());
                TLCGlobals.simulator = simulator;
                tool = simulator.getTool();
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
                tool = new FastTool(mainFile, configFile, resolver);
                checkDeadlock = checkDeadlock && tool.getModelConfig().getCheckDeadlock();
                if (isBFS())
                {
					TLCGlobals.mainChecker = new ModelChecker(tool, metadir, stateWriter, checkDeadlock, fromChkpt,
							FPSetFactory.getFPSetInitialized(fpSetConfiguration, metadir, new File(mainFile).getName()),
							startTime);
					modelCheckerMXWrapper = new ModelCheckerMXWrapper((ModelChecker) TLCGlobals.mainChecker, this);
					result = TLCGlobals.mainChecker.modelCheck();
                } else
                {
					TLCGlobals.mainChecker = new DFIDModelChecker(tool, metadir, stateWriter, checkDeadlock, fromChkpt, startTime);
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
			MP.flush();
			// Wait for the SpecTE generation to complete before termination.
			waitingOnGenerationCompletion.arriveAndAwaitAdvance();
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
    	sharedArguments.add(new UsageGenerator.Argument("-generateSpecTE", null,
														"if errors are encountered during model checking, generate\n"
															+ "a SpecTE tla/cfg file pair which encapsulates Init-Next\n"
															+ "definitions to specify the state conditions of the error\n"
															+ "state; this enables 'tool' mode. The generated SpecTE\n"
															+ "will include tool output as well as all non-Standard-\n"
															+ "Modules dependencies embeded in the module. To prevent\n"
															+ "the embedding of dependencies, add the parameter\n"
															+ "'nomonolith' to this declaration", true,
															"nomonolith"));
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
    	return this.runMode;
    }
    
    public long getSimulationBehaviorCountLimit() {
    	return TLC.traceNum;
    }
    
    public String getTraceFilePath() {
    	return this.traceFile;
    }
    
    public boolean isDeadlockCheckingEnabled() {
    	return this.checkDeadlock;
    }
    
    public boolean isStatesDirectoryMarkedForCleanup() {
    	return this.cleanup;
    }

    public String getMainFile() {
        return this.mainFile;
    }
    
    public String getConfigFile() {
    	return this.configFile;
    }
    
    public String getUserFile() {
    	return this.userFile;
    }

    public String getDumpFile() {
    	return this.dumpFile;
    }
    
    public boolean willGenerateErrorTraceSpec() {
    	return this.generateErrorTraceSpec;
    }
    
    public boolean isDumpDotFile() {
    	return this.asDot;
    }
    
    public boolean isDumpColorized() {
    	return this.colorize;
    }
    
    public boolean doesDumpHaveActionLabels() {
    	return this.actionLabels;
    }
    
    public boolean doesDumpIncludeSnapshots() {
    	return this.snapshot;
    }
    
    public int getTraceDepth() {
    	return this.traceDepth;
    }
    
    public boolean haveSeed() {
    	return !this.noSeed;
    }
    
    public long getSeed() {
    	return this.seed;
    }
    
    public long getAril() {
    	return this.aril;
    }
    
    public String getCheckpointRecoveryDirectory() {
    	return this.fromChkpt;
    }
    
    public int getFingerprintFunctionIndex() {
    	return this.fpIndex;
    }
    
    public FPSetConfiguration getFingerprintSetConfiguration() {
    	return new FPSetConfiguration(this.fpSetConfiguration);
    }

	public String getModelName() {
		return System.getProperty(MailSender.MODEL_NAME, this.mainFile);
	}
	
	public String getSpecName() {
		return System.getProperty(MailSender.SPEC_NAME, this.mainFile);
	}
}
