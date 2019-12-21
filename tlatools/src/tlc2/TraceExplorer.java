package tlc2;

import java.io.File;
import java.io.IOException;

import tlc2.input.MCOutputParser;
import tlc2.input.MCParser;
import tlc2.input.MCParserResults;
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
 */
public class TraceExplorer {
	private static final String GENERATE_SPEC_FUNCTION_PARAMETER_NAME = "-generateSpecTE";
	private static final String PRETTY_PRINT_FUNCTION_PARAMETER_NAME = "-prettyPrint";
	
    private static final String SOURCE_DIR_PARAMETER_NAME = "-source=";
    private static final String SPEC_NAME_PARAMETER_NAME = "-spec=";
    
    private static final String GENERATE_SPEC_OVERWRITE_PARAMETER_NAME = "-overwrite";
    
    private static final String SPEC_TE_MODULE_NAME = "SpecTE";
    
    private static final String SPEC_TE_INIT_ID = "SpecTEInit";
    private static final String SPEC_TE_NEXT_ID = "SpecTENext";
    private static final String SPEC_TE_ACTION_CONSTRAINT_ID = "SpecTEActionConstraint";
    
    private enum RunMode {
    	GENERATE_SPEC_TE, PRETTY_PRINT;
    }

    
    private File specGenerationSourceDirectory;
    private String specGenerationOriginalSpecName;
    
    private RunMode runMode;

    /**
     * @param commandLineArguments arguments, ostensibly from the command line, with which this instance will configure
     * 								itself.
     * @throws IllegalStateException if the instance could not configure itself for some know functionality execution
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
        } else {
        	return;
        }
    	
    	int index = 1;
    	
		specGenerationSourceDirectory = new File(System.getProperty("user.dir"));
		specGenerationOriginalSpecName = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		boolean overwriteSpecTE = false;

		boolean consumedAdditionalParameters = true;
		while (consumedAdditionalParameters) {
			if (index < args.length) {
				final String nextArg = args[index];
				
				if (nextArg.startsWith(SOURCE_DIR_PARAMETER_NAME)) {
					final String runDirectory = nextArg
							.substring(SOURCE_DIR_PARAMETER_NAME.length());
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
				} else if (nextArg.startsWith(SPEC_NAME_PARAMETER_NAME)) {
					specGenerationOriginalSpecName = nextArg
							.substring(SPEC_NAME_PARAMETER_NAME.length());
					index++;
				} else if (GENERATE_SPEC_OVERWRITE_PARAMETER_NAME.equals(nextArg)) {
					overwriteSpecTE = true;
					
					index++;
				} else {
    				consumedAdditionalParameters = false;
				}
			} else {
				consumedAdditionalParameters = false;
			}
		}
    	
    	String filename = specGenerationOriginalSpecName + TLAConstants.Files.OUTPUT_EXTENSION;
		final File mcOut = new File(specGenerationSourceDirectory, filename);
		if (!mcOut.exists()) {
			printErrorMessage("Error: source directory (" + specGenerationSourceDirectory + ") does not contain "
					+ filename);
			
			runMode = null;
			return;
		}
    	
		if (RunMode.GENERATE_SPEC_TE.equals(runMode)) {
			filename = specGenerationOriginalSpecName + TLAConstants.Files.TLA_EXTENSION;
			final File mcTLA = new File(specGenerationSourceDirectory, filename);
			if (!mcTLA.exists()) {
				printErrorMessage("Error: source directory (" + specGenerationSourceDirectory + ") does not contain "
						+ filename);
				
				runMode = null;
				return;
			}
	    	
			filename = specGenerationOriginalSpecName + TLAConstants.Files.CONFIG_EXTENSION;
			final File mcCFG = new File(specGenerationSourceDirectory, filename);
			if (!mcCFG.exists()) {
				printErrorMessage("Error: source directory (" + specGenerationSourceDirectory + ") does not contain "
						+ filename);
				
				runMode = null;
				return;
			}
			
			if (!overwriteSpecTE) {
				final File specTETLA = new File(specGenerationSourceDirectory,
												(SPEC_TE_MODULE_NAME + TLAConstants.Files.TLA_EXTENSION));

				if (specTETLA.exists()) {
					printErrorMessage("Error: specified source directory already contains " + specTETLA.getName()
							+ "; specify '" + GENERATE_SPEC_OVERWRITE_PARAMETER_NAME + "' to overwrite.");
					
					runMode = null;
					return;
				}
			}
		}
    }
    
    /**
     * @return an {@link EC} defined error code representing success or failure.
     */
    public int execute() throws Exception {
    	if (RunMode.GENERATE_SPEC_TE.equals(runMode)) {
    		final MCParser parser = new MCParser(specGenerationSourceDirectory, specGenerationOriginalSpecName);
    		final MCParserResults results = parser.parse();
    		
    		if (results.getOutputMessages().size() == 0) {
				MP.printMessage(EC.GENERAL, "The output file had no tool messages; was TLC not run with"
												+ " the '-tool' option when producing it?");

    			return EC.ExitStatus.ERROR;
    		} else if (results.getError() == null) {
				MP.printMessage(EC.GENERAL,
						"The output file contained no error-state messages, no SpecTE will be produced.");

    			return EC.NO_ERROR;
    		} else {
				try {
					writeSpecTEFile(results);

					return EC.NO_ERROR;
				} catch (final Exception e) { }
    		}
    	} else if (RunMode.PRETTY_PRINT.equals(runMode)) {
        	final String filename = specGenerationOriginalSpecName + TLAConstants.Files.OUTPUT_EXTENSION;
    		final File mcOut = new File(specGenerationSourceDirectory, filename);

    		try {
	    		MCOutputParser.prettyPrintToStream(System.out, mcOut);
				
				return EC.NO_ERROR;
    		} catch (final Exception e) { }
    	}
    	
		return EC.ExitStatus.ERROR;
    }
    
    private void writeSpecTEFile(final MCParserResults results) throws IOException {
    	final StringBuilder tlaBuffer = new StringBuilder();
    	final StringBuilder cfgBuffer = new StringBuilder();
    	SpecTraceExpressionWriter.addInitNextToBuffers(tlaBuffer, cfgBuffer, results.getError().getStates(), null,
    												  SPEC_TE_INIT_ID, SPEC_TE_NEXT_ID, SPEC_TE_ACTION_CONSTRAINT_ID,
    												  results.getOriginalNextOrSpecificationName());
    	
    	final boolean specExtendsTLC = results.getExtendedModules().contains("TLC");
		final TLACopier tlaCopier = new TLACopier(specGenerationOriginalSpecName, SPEC_TE_MODULE_NAME,
				specGenerationSourceDirectory, tlaBuffer.toString(), specExtendsTLC);
		tlaCopier.copy();
		
		final CFGCopier cfgCopier = new CFGCopier(specGenerationOriginalSpecName, SPEC_TE_MODULE_NAME,
				specGenerationSourceDirectory, cfgBuffer.toString());
		cfgCopier.copy();
    }
    
    private void printErrorMessage(final String message) {
    	MP.printError(EC.GENERAL, message);
    }
    
    
    private static void printUsageAndExit() {
    	System.out.println("Usage");
    	
    	System.out.println("\tTo generate a SpecTE file pair:");
    	System.out.println("\t\t\tjava tlc2.TraceExplorer -generateSpecTE \\\n"
				    			+ "\t\t\t\t[-source=_directory_containing_prior_run_output_] \\\n"
				    			+ "\t\t\t\t[-spec=SomethingOtherThanMC] \\\n"
				    			+ "\t\t\t\t[-overwrite]");
    	System.out.println("\t\to source defaults to CWD if not specified.");
    	System.out.println("\t\to spec defaults to 'MC' if not specified.");
    	System.out.println("\t\to if a SpecTE.tla already exists and overwrite is not specified, execution will halt.");
    	
    	System.out.println("");
    	
    	System.out.println("\tTo pretty print the error states of a previous run:");
    	System.out.println("\t\t\tjava tlc2.TraceExplorer -prettyPrint \\\n"
				    			+ "\t\t\t\t[-source=_directory_containing_prior_run_output_] \\\n"
				    			+ "\t\t\t\t[-spec=SomethingOtherThanMC]");
		System.out.println("\t\to source defaults to CWD if not specified.");
		System.out.println("\t\to spec defaults to 'MC' if not specified.");
    	
    	System.exit(-1);
    }
    
    /**
     * Ways to run this application:
     * 
     *  1. Generation of a 'SpecTE.tla' from an existing .tla/.out/.cfg triplet in which the .out contains
     *  	one or more MP.ERROR messages - see https://github.com/tlaplus/tlaplus/issues/393 for background:
     *  				java tlc2.TraceExplorer -generateSpecTE \
     *  						[-source=_directory_containing_prior_run_output_] \
     *  						[-spec=SomethingOtherThanMC] \
     *  						[-overwrite]
     *  	the source directory defaults to CWD if not defined, and spec defaults to MC if not defined; if overwrite
     *  	is not specified and a SpecTE.tla already exists in the source directory, execution will halt.
     *  
     *  2. Pretty print the error states from an existing .out file to {@link System#out}:
     *  				java tlc2.TraceExplorer -prettyPrint \
     *  						[-source=_directory_containing_prior_run_output_] \
     *  						[-spec=SomethingOtherThanMC]
     *  	the source directory defaults to CWD if not defined, and spec defaults to MC if not defined.
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
    	}
    }
}
