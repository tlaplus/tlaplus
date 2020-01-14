package tlc2;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.locks.ReentrantLock;

import tlc2.input.MCOutputParser;
import tlc2.input.MCOutputPipeConsumer;
import tlc2.input.MCParser;
import tlc2.input.MCParserResults;
import tlc2.model.MCError;
import tlc2.model.MCState;
import tlc2.output.CFGCopier;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.output.SpecTraceExpressionWriter;
import tlc2.output.TLACopier;
import util.TLAConstants;

/**
 * This is an application class which provides the following functionalities:
 * 
 * 		. given a directory of a previously run model check (containing a .tla/.cfg/.out triplet), produce a "SpecTE"
 * 				.tla / .cfg file pair
 * 		. given a directory of a previously run model check (containing a .out file), dump a pretty print of the
 *				errors states to {@link System#out}
 * 		. given a directory of a previously run model check (containing a .tla/.cfg/.out triplet) and a file of
 * 				trace expressions, one per line, produce a "SpecTE" file pair, then run a model check
 * 				evaluating the expressions, writing the triplet TE.tla, TE.cfg, TE.out
 * 		. given a directory of a previously generated SpecTE file pair and a file of trace expressions, one per line,
 * 				run a model check evaluating the expressions, writing the triplet TE.tla, TE.cfg, TE.out
 *		. given an already executed output pipe consumer, generated a "SpecTE" .tla / .cfg pair
 */
public class TraceExplorer {
	private static final String GENERATE_SPEC_FUNCTION_PARAMETER_NAME = "-generateSpecTE";
	private static final String PRETTY_PRINT_FUNCTION_PARAMETER_NAME = "-prettyPrint";
	private static final String QUASI_REPL_PARAMETER_NAME = "-replBis";
	private static final String TRACE_EXPRESSIONS_FUNCTION_PARAMETER_NAME = "-traceExpressions";

    private static final String EXPRESSIONS_FILE_PARAMETER_NAME = "-expressionsFile=";
    private static final String MODEL_CHECK_TLC_ARGUMENTS_PARAMETER_NAME = "-tlcArguments=";

    private static final String SOURCE_DIR_PARAMETER_NAME = "-source=";
    private static final String GENERATE_SPEC_OVERWRITE_PARAMETER_NAME = "-overwrite";
    
    static final String SPEC_TE_INIT_ID = "_SpecTEInit";
    static final String SPEC_TE_NEXT_ID = "_SpecTENext";
    private static final String SPEC_TE_ACTION_CONSTRAINT_ID = "_SpecTEActionConstraint";
    
    // <parameter name, whether the parameter takes an argument>
    private static final HashMap<String, Boolean> TLC_ARGUMENTS_TO_IGNORE;
    
    static {
    	TLC_ARGUMENTS_TO_IGNORE = new HashMap<>();
    	
    	TLC_ARGUMENTS_TO_IGNORE.put("-config", Boolean.TRUE);
    	TLC_ARGUMENTS_TO_IGNORE.put("-metadir", Boolean.TRUE);
    	TLC_ARGUMENTS_TO_IGNORE.put("-tool", Boolean.FALSE);
    }
    
    
    /**
	 * @param sourceDirectory
	 * @param originalSpecName
	 * @param results
	 * @param error
	 * @return an array of length two; the 0-index is the location to the
	 *         destination TLA file, and the 1-index is that of the CFG file
	 * @throws IOException
	 */
    public static File[] writeSpecTEFiles(final File sourceDirectory, final String originalSpecName,
    									  final MCParserResults results, final MCError error) throws IOException {
    	final StringBuilder tlaBuffer = new StringBuilder();
    	final StringBuilder cfgBuffer = new StringBuilder();
    	final List<MCState> trace = error.getStates();
    	SpecTraceExpressionWriter.addInitNextToBuffers(tlaBuffer, cfgBuffer, trace, null,
    												   SPEC_TE_INIT_ID, SPEC_TE_NEXT_ID, SPEC_TE_ACTION_CONSTRAINT_ID,
    												   results.getOriginalNextOrSpecificationName());
    	SpecTraceExpressionWriter.addTraceFunctionToBuffers(tlaBuffer, cfgBuffer, trace);
    	
    	final List<String> extendedModules = results.getOriginalExtendedModules();
    	final boolean specExtendsTLC = extendedModules.contains(TLAConstants.BuiltInModules.TLC);
    	final boolean specExtendsToolbox = extendedModules.contains(TLAConstants.BuiltInModules.TRACE_EXPRESSIONS);
		final TLACopier tlaCopier = new TLACopier(originalSpecName, TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME,
												  sourceDirectory, tlaBuffer.toString(), specExtendsTLC,
												  specExtendsToolbox);
		tlaCopier.copy();
		MP.printMessage(EC.GENERAL,
						"The file " + tlaCopier.getDestinationFile().getAbsolutePath() + " has been created.");
		
		final CFGCopier cfgCopier = new CFGCopier(originalSpecName, TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME,
												  sourceDirectory, cfgBuffer.toString());
		cfgCopier.copy();
		MP.printMessage(EC.GENERAL,
						"The file " + cfgCopier.getDestinationFile().getAbsolutePath() + " has been created.");
		
		return new File[] { tlaCopier.getDestinationFile(), cfgCopier.getDestinationFile() };
    }
    
    
    private enum RunMode {
    	GENERATE_SPEC_TE, PRETTY_PRINT, GENERATE_FROM_TLC_RUN, QUASI_REPL, TRACE_EXPLORATION;
    }

    
    private File specGenerationSourceDirectory;
    private String specGenerationOriginalSpecName;
    private boolean expectedOutputFromStdIn;
    private boolean overwriteGeneratedFiles;
    
    private List<String> expressions;
    private List<String> tlcArguments;
    
    private String replSpecName;
    private File temporaryREPLSpec;
    
    private RunMode runMode;

    /**
     * @param commandLineArguments arguments, ostensibly from the command line, with which this instance will configure
     * 								itself.
     */
    public TraceExplorer(final String[] commandLineArguments) {
    	processArguments(commandLineArguments);
    	
    	if (runMode == null) {
			throw new IllegalStateException(
					"The provided arguments were not sufficient to configure the TraceExplorer.");
    	}
    }
    
    protected final void processArguments(final String[] args) {
    	if (args[0].equals(GENERATE_SPEC_FUNCTION_PARAMETER_NAME)) {
        	runMode = RunMode.GENERATE_SPEC_TE;
        } else if (args[0].equals(PRETTY_PRINT_FUNCTION_PARAMETER_NAME)) {
        	runMode = RunMode.PRETTY_PRINT;
        } else if (args[0].equals(TRACE_EXPRESSIONS_FUNCTION_PARAMETER_NAME)) {
        	runMode = RunMode.TRACE_EXPLORATION;
    		tlcArguments = new ArrayList<>();
        } else if (args[0].equals(QUASI_REPL_PARAMETER_NAME)) {
        	runMode = RunMode.QUASI_REPL;
    		tlcArguments = new ArrayList<>();
        } else {
        	runMode = null;
        	return;
        }
    	
    	int index = 1;
    	
		specGenerationSourceDirectory = new File(System.getProperty("user.dir"));
		specGenerationOriginalSpecName = args[args.length - 1];
		expectedOutputFromStdIn = (specGenerationOriginalSpecName.charAt(0) == '-');
		if (expectedOutputFromStdIn) {
			specGenerationOriginalSpecName = null;
		} else if (RunMode.QUASI_REPL.equals(runMode)) {
			printUsageAndExit();
		}
		overwriteGeneratedFiles = false;

		String expressionsSourceFilename = null;
		
		boolean consumedAdditionalParameters = true;
		final int upperIndex = expectedOutputFromStdIn ? args.length : (args.length - 1);
		while (consumedAdditionalParameters) {
			if (index < upperIndex) {
				final String nextArg = args[index];
				
				if (nextArg.startsWith(SOURCE_DIR_PARAMETER_NAME)) {
					final String runDirectory = nextArg.substring(SOURCE_DIR_PARAMETER_NAME.length());
            		final File f = new File(runDirectory);
            		
            		if (!f.exists()) {
            			printErrorMessage("Error: specified source directory does not exist.");
            			return;
            		}
            		
            		if (!f.isDirectory()) {
            			printErrorMessage("Error: specified source directory is not a directory.");
            			return;
            		}
            		specGenerationSourceDirectory = f;

					index++;
				} else if (GENERATE_SPEC_OVERWRITE_PARAMETER_NAME.equals(nextArg)) {
					overwriteGeneratedFiles = true;
					
					index++;
				} else if (nextArg.startsWith(EXPRESSIONS_FILE_PARAMETER_NAME)) {
					expressionsSourceFilename = nextArg.substring(EXPRESSIONS_FILE_PARAMETER_NAME.length());
					
					index++;
				} else if (nextArg.startsWith(MODEL_CHECK_TLC_ARGUMENTS_PARAMETER_NAME)) {
					final String argumentList = nextArg.substring(MODEL_CHECK_TLC_ARGUMENTS_PARAMETER_NAME.length());
					final String[] arguments = argumentList.split(" ");
					int argIndex = 0;
					
					while (argIndex < arguments.length) {
						final String argument = arguments[argIndex];
						final Boolean ignoreAdditionalParameter = TLC_ARGUMENTS_TO_IGNORE.get(argument);
						
						if (ignoreAdditionalParameter == null) {
							tlcArguments.add(argument);
						} else {
							if (ignoreAdditionalParameter.booleanValue()) {
								argIndex++;
							}
						}
						
						argIndex++;
					}
					
					index++;
				} else {
    				consumedAdditionalParameters = false;
				}
			} else {
				consumedAdditionalParameters = false;
			}
		}
		
		if (RunMode.TRACE_EXPLORATION.equals(runMode) || RunMode.QUASI_REPL.equals(runMode)) {
			if (expressionsSourceFilename == null) {
    			printErrorMessage("Error: no expressions file specified.");
				runMode = null;
				return;
			}
			
			final File sourceDirFile = new File(specGenerationSourceDirectory, expressionsSourceFilename);
			final File absoluteFile = new File(expressionsSourceFilename);
			final File f;
			if (sourceDirFile.exists()) {
				f = sourceDirFile;
			} else if (absoluteFile.exists()) {
				f = absoluteFile;
			} else {
				printErrorMessage("Error: an expressions file could be found at neither "
										+ sourceDirFile.getAbsolutePath()
										+ " nor " + absoluteFile.getAbsolutePath());
				runMode = null;
				return;
			}

			try {
				expressions = new ArrayList<>();
				try (final BufferedReader br = new BufferedReader(new FileReader(f))) {
					String line;
					while ((line = br.readLine()) != null) {
						expressions.add(line);
					}
				}
			} catch (final IOException e) {
				printErrorMessage("Error: encountered an exception reading from expressions file "
									+ f.getAbsolutePath() + " :: " + e.getMessage());
				runMode = null;
				return;
			}

			if (RunMode.TRACE_EXPLORATION.equals(runMode)) {
				tlcArguments.add("-config");
				tlcArguments.add(TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME 
									+ TLAConstants.Files.CONFIG_EXTENSION);
				
				tlcArguments.add("-tool");
			} else {
				replSpecName = "repl"; //"REPL_" + System.currentTimeMillis();
				temporaryREPLSpec = new File(specGenerationSourceDirectory,
											 replSpecName + TLAConstants.Files.TLA_EXTENSION);
				temporaryREPLSpec.deleteOnExit();
			}

			tlcArguments.add("-metadir");
			tlcArguments.add(specGenerationSourceDirectory.getAbsolutePath());
			
			if (RunMode.TRACE_EXPLORATION.equals(runMode)) {
				tlcArguments.add(TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME);
			} else {
				tlcArguments.add(replSpecName);
			}
		}
     }
    
    /**
     * @return an {@link EC} defined error code representing success or failure.
     */
    public int execute() throws Exception {
    	if (RunMode.QUASI_REPL.equals(runMode)) {
    		return performREPL();
    	} else if (expectedOutputFromStdIn) {
    		return executeStreaming();
    	} else {
    		return executeNonStreaming();
    	}
    }
    
    private int executeNonStreaming() throws Exception {
    	if (!performPreFlightFileChecks()) {
			throw new IllegalStateException("There was an issue with the input, "
												+ TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME + ", or "
												+ TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME + " file.");
    	}
    	
		final boolean specifiedModuleIsSpecTE
					= specGenerationOriginalSpecName.equals(TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME);
		final boolean needGenerateSpecTE = RunMode.GENERATE_SPEC_TE.equals(runMode) 
											|| (!specifiedModuleIsSpecTE && RunMode.TRACE_EXPLORATION.equals(runMode));
    	if (needGenerateSpecTE) {
			final MCParser parser = new MCParser(specGenerationSourceDirectory, specGenerationOriginalSpecName);
    		final MCParserResults results = parser.parse();
    		
    		if (results.getOutputMessages().size() == 0) {
				MP.printMessage(EC.GENERAL, "The output file had no tool messages; was TLC not run with"
												+ " the '-tool' option when producing it?");

    			return EC.ExitStatus.ERROR;
    		} else if (results.getError() == null) {
    			final String msg;
    			if (RunMode.GENERATE_SPEC_TE.equals(runMode)) {
    				msg = "The output file contained no error-state messages, no "
    							+ TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME + " will be produced.";
    			} else {
    				msg = "The output file contained no error-state messages, no "
								+ TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME + " nor "
								+ TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME + " will be produced, and, so, "
								+ "no trace expressions will be evaluated.";
    			}
				MP.printMessage(EC.GENERAL, msg);

    			return EC.NO_ERROR;
    		} else {
				try {
					writeSpecTEFiles(results, results.getError());

					if (RunMode.GENERATE_SPEC_TE.equals(runMode)) {
						return EC.NO_ERROR;
					} else if (RunMode.TRACE_EXPLORATION.equals(runMode)) { 	// currently always true
			    		return performTraceExploration();
			    	}
				} catch (final Exception e) { }
    		}
    	} else if (RunMode.PRETTY_PRINT.equals(runMode)) {
    		try {
	    		MCOutputParser.prettyPrintToStream(System.out, specGenerationSourceDirectory,
	    										   specGenerationOriginalSpecName);
				
				return EC.NO_ERROR;
    		} catch (final Exception e) { }
    	}
    	    	
		return EC.ExitStatus.ERROR;
    }
    
    private int executeStreaming() throws Exception {
    	final AtomicBoolean mcParserCompleted = new AtomicBoolean(false);
    	final ReentrantLock parseLock = new ReentrantLock();
    	final ArrayList<MCParser> parserList = new ArrayList<>(1);
		final MCOutputPipeConsumer.ConsumerLifespanListener listener
							= new MCOutputPipeConsumer.ConsumerLifespanListener() {
			@Override
			public void consumptionFoundSourceDirectoryAndSpecName(MCOutputPipeConsumer consumer) {
				specGenerationSourceDirectory = consumer.getSourceDirectory();
				specGenerationOriginalSpecName = consumer.getSpecName();
				
				final boolean specifiedModuleIsSpecTE
							= specGenerationOriginalSpecName.equals(TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME);
				final boolean needGenerateSpecTE
							= RunMode.GENERATE_SPEC_TE.equals(runMode)
											|| (!specifiedModuleIsSpecTE && RunMode.TRACE_EXPLORATION.equals(runMode));

				if (!performPreFlightFileChecks()) {
					throw new IllegalStateException("There was an issue with the input, "
														+ TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME + ", or "
														+ TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME + " file.");
				}

				if (needGenerateSpecTE) {
					MP.printMessage(EC.GENERAL,
							"Have encountered the source spec in the output logging, will begin parsing of those assets now.");
					
					final Runnable r = () -> {
						final MCParser parser
								= new MCParser(specGenerationSourceDirectory, specGenerationOriginalSpecName, true);
						parserList.add(parser);
						
						parseLock.lock();
						try {
							parser.parse();
						} finally {
							mcParserCompleted.set(true);
							parseLock.unlock();
						}
					};
					(new Thread(r)).start();
				}
			}
		};
		final MCOutputPipeConsumer pipeConsumer = new MCOutputPipeConsumer(System.in, listener);
		
		MP.printMessage(EC.GENERAL, "TraceExplorer is expecting input on stdin...");

		pipeConsumer.consumeOutput(false);
		
		if (pipeConsumer.outputHadNoToolMessages()) {
			MP.printMessage(EC.GENERAL, "The output had no tool messages; was TLC not run with"
					+ " the '-tool' option when producing it?");

			return EC.ExitStatus.ERROR;
		}

		MP.printMessage(EC.GENERAL, "Have received the final output logging message - finishing TraceExplorer work.");

		final boolean specifiedModuleIsSpecTE
				= specGenerationOriginalSpecName.equals(TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME);
		final boolean needGenerateSpecTE
				= RunMode.GENERATE_SPEC_TE.equals(runMode)
								|| (!specifiedModuleIsSpecTE && RunMode.TRACE_EXPLORATION.equals(runMode));
    	if (needGenerateSpecTE) {
    		if (pipeConsumer.getError() == null) {
    			final String msg;
    			if (RunMode.GENERATE_SPEC_TE.equals(runMode)) {
    				msg = "The output contained no error-state messages, no "
    							+ TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME + " will be produced.";
    			} else {
    				msg = "The output contained no error-state messages, no "
								+ TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME + " nor "
								+ TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME + " will be produced, and, so, "
								+ "no trace expressions will be evaluated.";
    			}
				MP.printMessage(EC.GENERAL, msg);

    			return EC.NO_ERROR;
    		} else {
        		if (!mcParserCompleted.get()) {
        			parseLock.lock();
        		}
        		final MCParserResults results = parserList.get(0).getParseResults();
    			
				try {
					writeSpecTEFiles(results, pipeConsumer.getError());

					if (RunMode.GENERATE_SPEC_TE.equals(runMode)) {
						return EC.NO_ERROR;
					} else if (RunMode.TRACE_EXPLORATION.equals(runMode)) { 	// currently always true
			    		return performTraceExploration();
			    	}
				} catch (final Exception e) { }
    		}
    	} else if (RunMode.PRETTY_PRINT.equals(runMode)) {
    		if (pipeConsumer.getError() == null) {
    			MP.printMessage(EC.GENERAL, "The output contained no error-state messages; there is nothing to display.");
				
				return EC.NO_ERROR;
    		} else {
        		try {
    	    		MCOutputParser.prettyPrintToStream(System.out, pipeConsumer.getError());
    				
    				return EC.NO_ERROR;
        		} catch (final Exception e) { }
    		}
    	}
    	
		return EC.ExitStatus.ERROR;
    }
    
    private int performREPL() throws IOException {
    	final REPLSpecWriter writer = new REPLSpecWriter(replSpecName, expressions);
    	final File cfgFile = new File(specGenerationSourceDirectory, replSpecName + TLAConstants.Files.CONFIG_EXTENSION);
    	cfgFile.deleteOnExit();
    	writer.writeFiles(temporaryREPLSpec, cfgFile);

    	final REPLSpecWriter.REPLLogConsumerStream outputStream = new REPLSpecWriter.REPLLogConsumerStream();
		final TLCRunner tlcRunner = new TLCRunner(tlcArguments, outputStream);
		tlcRunner.setSilenceStdOut(true);
		final int errorCode = tlcRunner.run();
		
		System.out.println(String.join("\n", expressions));
		System.out.println("\t" + TLAConstants.EQ);
		// TODO indent on multi-line
		System.out.println("\t\t" + outputStream.getCollectedContent());

    	return errorCode;
    }
    
	private int performTraceExploration() throws IOException {
		final File tlaFile = new File(specGenerationSourceDirectory,
				TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME + TLAConstants.Files.TLA_EXTENSION);
		final TraceExpressionExplorerSpecWriter writer = new TraceExpressionExplorerSpecWriter(expressions);
		final String configContent = writer.getConfigBuffer().toString();
		writer.writeFiles(tlaFile, null);

		final CFGCopier cfgCopier = new CFGCopier(TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME,
				TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME, specGenerationSourceDirectory, configContent);
		cfgCopier.copy();

		final File outFile = new File(specGenerationSourceDirectory,
				TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME + TLAConstants.Files.OUTPUT_EXTENSION);
		final TLCRunner tlcRunner = new TLCRunner(tlcArguments, outFile);
		System.out.println("Forking TLC...");
		final int errorCode = tlcRunner.run();

		MCOutputParser.prettyPrintToStream(System.out, specGenerationSourceDirectory,
										   TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME);

		return errorCode;
	}

    private boolean performPreFlightFileChecks() {
		final boolean specifiedModuleIsSpecTE
				= specGenerationOriginalSpecName.equals(TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME);
		final boolean outputShouldExist = !expectedOutputFromStdIn 
											|| (specifiedModuleIsSpecTE && RunMode.TRACE_EXPLORATION.equals(runMode));

		String filename;
    	
    	if (outputShouldExist) {
    		filename = specGenerationOriginalSpecName + TLAConstants.Files.OUTPUT_EXTENSION;
    		final File outputFile = new File(specGenerationSourceDirectory, filename);
    		if (!outputFile.exists()) {
    			printErrorMessage("Error: source directory (" + specGenerationSourceDirectory + ") does not contain "
    					+ filename);
    			
    			runMode = null;
    			return false;
    		}
    	}
    	
		if (RunMode.GENERATE_SPEC_TE.equals(runMode) || RunMode.TRACE_EXPLORATION.equals(runMode)) {
			filename = specGenerationOriginalSpecName + TLAConstants.Files.TLA_EXTENSION;
			final File tlaFile = new File(specGenerationSourceDirectory, filename);
			if (!tlaFile.exists()) {
				printErrorMessage("Error: source directory (" + specGenerationSourceDirectory + ") does not contain "
						+ filename);
				
				runMode = null;
				return false;
			}
	    	
			filename = specGenerationOriginalSpecName + TLAConstants.Files.CONFIG_EXTENSION;
			final File configFile = new File(specGenerationSourceDirectory, filename);
			if (!configFile.exists()) {
				printErrorMessage("Error: source directory (" + specGenerationSourceDirectory + ") does not contain "
						+ filename);
				
				runMode = null;
				return false;
			}
			
			if (!overwriteGeneratedFiles) {
				if (!specifiedModuleIsSpecTE) {
					final File specTETLA = new File(specGenerationSourceDirectory,
							(TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME + TLAConstants.Files.TLA_EXTENSION));

					if (specTETLA.exists()) {
						printErrorMessage("Error: specified source directory already contains " + specTETLA.getName()
								+ "; specify '" + GENERATE_SPEC_OVERWRITE_PARAMETER_NAME + "' to overwrite.");

						runMode = null;
						return false;
					}
				}
				
				if (RunMode.TRACE_EXPLORATION.equals(runMode)) {
					final File teTLA = new File(specGenerationSourceDirectory,
								(TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME + TLAConstants.Files.TLA_EXTENSION));

					if (teTLA.exists()) {
						printErrorMessage("Error: specified source directory already contains " + teTLA.getName()
								+ "; specify '" + GENERATE_SPEC_OVERWRITE_PARAMETER_NAME + "' to overwrite.");

						runMode = null;
						return false;
					}
				}
			}
		}
		
		return true;
    }
    
    private void writeSpecTEFiles(final MCParserResults results, final MCError error) throws IOException {
    	writeSpecTEFiles(specGenerationSourceDirectory, specGenerationOriginalSpecName, results, error);
    }
    
    private void printErrorMessage(final String message) {
    	MP.printError(EC.GENERAL, message);
    }
    
    
    private static void printUsageAndExit() {
    	System.out.println("Usage");

    	System.out.println("\tTo evaluate trace expressions:");
    	System.out.println("\t\t\tjava tlc2.TraceExplorer " + TRACE_EXPRESSIONS_FUNCTION_PARAMETER_NAME + " \\\n"
    							+ "\t\t\t\t" + EXPRESSIONS_FILE_PARAMETER_NAME
    										 + "_file_containing_expressions_one_per_line_ \\\n"
				    			+ "\t\t\t\t[" + MODEL_CHECK_TLC_ARGUMENTS_PARAMETER_NAME
				    						  + "\"-some -other 2 -tlc arguments\"] \\\n"
				    			+ "\t\t\t\t[" + SOURCE_DIR_PARAMETER_NAME
				    						  + "_directory_containing_prior_run_output_] \\\n"
				    			+ "\t\t\t\t[" + GENERATE_SPEC_OVERWRITE_PARAMETER_NAME + "] \\\n"
				    			+ "\t\t\t\tSpecName");
    	System.out.println("\t\to the expressions file must either exist in the source directory or be a full path");
    	System.out.println("\t\to if TLC arguments are specified (all within quotes) they will be passed on to TLC "
    							+ "when performing the model check; -config, -tool, and -metadir will be ignored, "
    							+ "if specified.");
    	System.out.println("\t\to source defaults to CWD if not specified.");
    	System.out.println("\t\to if a " + TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME + ".tla, or "
    							+ TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME
    							+ ".tla, already exists and overwrite is not specified, execution will halt.");
    	System.out.println("\t\to if no SpecName is specified, output will be expected to arrive via stdin; "
    							+ SOURCE_DIR_PARAMETER_NAME + " will be ignored in this case.");
    	System.out.println("\t\to if SpecName is specified and it is anything other than "
    							+ TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME
    							+ ", generation of this file pair will occur first");
    	
    	System.out.println("");
    	
    	System.out.println("\tTo perform a one off evaluation of an expression:");
    	System.out.println("\t\t\tjava tlc2.TraceExplorer " + QUASI_REPL_PARAMETER_NAME + " \\\n"
    							+ "\t\t\t\t" + EXPRESSIONS_FILE_PARAMETER_NAME
    										 + "_file_containing_an_expression_to_evaluate_ \\\n"
				    			+ "\t\t\t\t[" + MODEL_CHECK_TLC_ARGUMENTS_PARAMETER_NAME
				    						  + "\"-some -other 2 -tlc arguments\"]");
    	System.out.println("\t\to the expressions file must either exist in the CWD or be a full path");
    	System.out.println("\t\to if TLC arguments are specified (all within quotes) they will be passed on to TLC "
    							+ "when performing the model check; -config, -tool, and -metadir will be ignored, "
    							+ "if specified.");
    	System.out.println("\t\to if a SpecName is specified, this usage will be printed and execution will hault");
    	
    	System.out.println("");
    	
    	System.out.println("\tTo generate a " + TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME + " file pair:");
    	System.out.println("\t\t\tjava tlc2.TraceExplorer " + GENERATE_SPEC_FUNCTION_PARAMETER_NAME + " \\\n"
				    			+ "\t\t\t\t[" + SOURCE_DIR_PARAMETER_NAME
				    						  + "_directory_containing_prior_run_output_] \\\n"
				    			+ "\t\t\t\t[" + GENERATE_SPEC_OVERWRITE_PARAMETER_NAME + "] \\\n"
				    			+ "\t\t\t\tSpecName");
    	System.out.println("\t\to source defaults to CWD if not specified.");
    	System.out.println("\t\to if a " + TLAConstants.TraceExplore.ERROR_STATES_MODULE_NAME + ".tla already exists and overwrite "
    							+ "is not specified, execution will halt.");
    	System.out.println("\t\to if no SpecName is specified, output will be expected to arrive via stdin; "
    							+ SOURCE_DIR_PARAMETER_NAME + " will be ignored in this case.");
    	
    	System.out.println("");
    	
    	System.out.println("\tTo pretty print the error states of a previous run:");
    	System.out.println("\t\t\tjava tlc2.TraceExplorer " + PRETTY_PRINT_FUNCTION_PARAMETER_NAME + " \\\n"
				    			+ "\t\t\t\t[" + SOURCE_DIR_PARAMETER_NAME
				    						  + "_directory_containing_prior_run_output_] \\\n"
				    			+ "\t\t\t\tSpecName");
		System.out.println("\t\to source defaults to CWD if not specified.");
    	System.out.println("\t\to if no SpecName is specified, output will be expected to arrive via stdin; "
								+ SOURCE_DIR_PARAMETER_NAME + " will be ignored in this case.");
    	
    	System.exit(-1);
    }
    
    /**
     * Ways to run this application:
     * 
     *  1. Evaluation of trace expressions from afrom an existing .tla/.out/.cfg triplet in which the .out contains
     *  	one or more MP.ERROR messages - see https://github.com/tlaplus/tlaplus/issues/393 for background:
     *  				java tlc2.TraceExplorer -traceExpressions \
     *  						-expressionsFile=_file_containing_expressions_one_per_line_ \
     *  						[-tlcArguments=_directory_containing_prior_run_output_] \
     *  						[-source=_directory_containing_prior_run_output_] \
     *  						[-overwrite] \
     *  						SpecName
     *  	the source directory defaults to CWD if not defined; the expressions file must either exist in the source
     *  	directory or be a full path; if TLC arguments are specified (all within quotes) they will be passed on to
     *  	TLC when performing the model check; -config, -tool, and -metadir will be ignored, if specified;  if no
     *  	SpecName is specified then we will expect the output data to arrive on stdin - anything specified via
     *  	-source will be ignore in this case as we will derive that from the output log content.
     *  
     *  2. Evaluation of an expression, ala REPL-ese:
     *  				java tlc2.TraceExplorer -replBis \
     *  						-expressionsFile=_file_containing_expressions_to_evaluate_ \
     *  						[-tlcArguments=_directory_containing_prior_run_output_]
     *  	the expressions file must either exist in the source directory or be a full path; if TLC arguments are
     *  	specified (all within quotes) they will be passed on to TLC when performing the model check; -config,
     *  	-tool, and -metadir will be ignored, if specified
     *  
     *  3. Generation of a 'SpecTE.tla' from an existing .tla/.out/.cfg triplet in which the .out contains
     *  	one or more MP.ERROR messages - see https://github.com/tlaplus/tlaplus/issues/393 for background:
     *  				java tlc2.TraceExplorer -generateSpecTE \
     *  						[-source=_directory_containing_prior_run_output_] \
     *  						[-overwrite] \
     *  						SpecName
     *  	the source directory defaults to CWD if not defined; if overwrite is not specified and a SpecTE.tla
     *  	already exists in the source directory, execution will halt; if no SpecName is specified then we
     *  	will expect the output data to arrive on stdin - anything specified via -source will be ignore in this
     *  	case as we will derive that from the output log content.
     *  
     *  4. Pretty print the error states from an existing .out file to {@link System#out}:
     *  				java tlc2.TraceExplorer -prettyPrint \
     *  						[-source=_directory_containing_prior_run_output_] \
     *  						SpecName
     *  	the source directory defaults to CWD if not defined; if no SpecName is specified then we
     *  	will expect the output data to arrive on stdin - anything specified via -source will be ignore in this
     *  	case as we will derive that from the output log content.
     */
    public static void main(final String[] args) {
    	if (args.length == 0) {
    		printUsageAndExit();
    	}
    	
    	try {
        	final TraceExplorer te = new TraceExplorer(args);
	    	final int returnCode = te.execute();
	    	
	    	System.exit(returnCode);
    	} catch (final Exception e) {
    		System.err.println("Caught exception: " + e.getLocalizedMessage());
    		
    		printUsageAndExit();
    	}
    }
}
