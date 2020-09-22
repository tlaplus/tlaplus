package tlc2;

import java.util.Optional;

import tlc2.tool.fp.MultiFPSet;
import tlc2.util.FP64;
import util.FileUtil;
import util.TLAConstants;

/**
 * Parses command line options.
 * 
 * Instructions for adding a new command line option:
 *  1. Add a field to this class representing your option
 *  	- Use boolean for flags and Optional for parameters
 *  2. Add parsing logic to the parse method
 *  3. Add validation logic to the validate method (if required)
 *  4. Add transformation logic to the transform method (if required)
 *  5. Add tests for your new option for all of those methods
 *  6. Add text describing your option to the help output
 * 
 * Try to keep the parse method focused on content-unaware parsing, not validation.
 * For example, if your option requires an integer in a certain range, this constraint
 * should not be checked & enforced during the parsing process. The old method mixed
 * the three stages (parsing, validation, use) together and the result was an enormous
 * unmaintainable, untestable confusing mess. It is best to keep these separate. It
 * is also best to avoid processing, interpreting, or transforming the user input
 * outside of the transform function.
 * 
 * Since this parsing code was all written in-house instead of using a standardized
 * command line option parsing library, it has developed some odd semantics which
 * must be preserved for backwards compatibility. For example, the TLA+ spec to
 * model check is not identified with any sort of flag, like -spec. The user is also
 * not required to give the spec path in a certain position, like at the end of all
 * the options. Indeed, the user is not required to provide a TLA+ spec at all; TLC
 * will automatically search the execution directory for a .jar if one is not given.
 * This places some unfortunate restrictions on our parsing & error reporting
 * abilities. For example, -lncheck requires a string argument after it; how are we
 * to report an error if the user inputs this command?
 * 
 *     java.exe tlc2.TLC -lncheck Spec.tla
 *     
 * The -lncheck option greedily consumes Spec.tla as its string argument, leaving
 * no TLA+ spec given as an option; TLC will search the current directory and
 * (hopefully) find no .jar file to execute. Thus this manifests as a "Missing
 * input TLA+ module" error instead of a -lncheck error. There is no general way
 * to distinguish TLA+ spec arguments from -lncheck arguments.
 * 
 * Things are even worse with the -simulate flag, where the string argument is
 * optional. Here the following semantics were chosen (or arose): greedily consume
 * the next string as an optional argument to -simulate, unless it is the final
 * string in the array of arguments, in which case do not consume it as it may
 * be the specification file path. Thus we support this (common) command:
 * 
 *     java.exe tlc2.TLC -simulate Spec.tla
 * 
 * But do not support this (less common) command:
 * 
 *     java.exe tlc2.TLC -simulate num=1234
 *
 * where the user specifies the optional argument to -simulate, but does not provide
 * a TLA+ spec (so TLC will look for a .jar in the current directory). Instead, the
 * num=1234 argument will be interpreted as the TLA+ spec argument.
 * 
 * There's also a problem with this command:
 * 
 * 		java.exe tlc2.TLC Spec.tla -simulate num=1234
 * 
 * where the num=1234 argument is interpreted as a second TLA+ spec, so TLC outputs
 * an error saying so.
 * 
 * The upshot of all of this is you are defining a new command line option, please
 * do not give it an optional parameter like with -simulate. It will still have the
 * error reporting issues outlined up above, but this is less bad.
 */
public class CommandLineOptions
{
	/**
	 * Whether to run TLC in simulation mode.
	 */
	public boolean simulationModeFlag = false;
	
	/**
	 * The maximum number of traces/behaviors to generate in simulation mode.
	 */
	public Optional<Long> simulationBehaviorCountLimit = Optional.empty();
	
	/**
	 * File to which to write simulation traces.
	 */
	public Optional<String> simulationTraceFile = Optional.empty();
	
	/**
	 * Whether to model check the spec (ignored).
	 */
	public boolean modelCheckFlag = false;
	
	/**
	 * Whether to only print state differences in traces.
	 */
	public boolean onlyPrintStateTraceDiffsFlag = false;
	
	/**
	 * Whether to check for deadlock.
	 */
	public boolean doNotCheckDeadlockFlag = false;
	
	/**
	 * Whether to clean states directory.
	 */
	public boolean cleanStatesDirectoryFlag = false;
	
	/**
	 * Whether to print warnings.
	 */
	public boolean doNotPrintWarningsFlag = false;
	
	/**
	 * Whether to apply GZip to input/output stream.
	 */
	public boolean useGZipFlag = false;
	
	/**
	 * Whether to expand values in print statements.
	 */
	public boolean terseOutputFlag = false;
	
	/**
	 * Whether to continue running after an invariant is violated.
	 */
	public boolean continueAfterInvariantViolationFlag = false;
	
	/**
	 * Whether to apply a VIEW when printing out states.
	 */
	public boolean useViewFlag = false;
	
	/**
	 * Whether to print debugging information.
	 */
	public boolean debugFlag = false;
	
	/**
	 * Whether to output messages in an easily-parsed format.
	 */
	public boolean useToolOutputFormatFlag = false;
	
	/**
	 * Whether to generate a spec to re-execute any encountered error trace.
	 */
	public boolean generateErrorTraceSpecFlag = false;
	
	/**
	 * Whether to create a monolithic error trace spec.
	 */
	public boolean noMonolithErrorTraceSpecFlag = false;
	
	/**
	 * TODO: find out what this does.
	 */
	public Optional<String> livenessCheck = Optional.empty();
	
	/**
	 * Path to the model checking configuration file.
	 */
	public Optional<String> configurationFilePath = Optional.empty();
	
	/**
	 * Path to the state dump file.
	 */
	public Optional<String> dumpFilePath = Optional.empty();
	
	/**
	 * Options controlling how states are dumped to file.
	 */
	public Optional<DumpFileControls> dumpFileOptions = Optional.empty();
	
	/**
	 * Number of minutes between collection of coverage information.
	 */
	public Optional<Integer> coverageIntervalInMinutes = Optional.empty();
	
	/**
	 * Number of minutes between checkpoints.
	 */
	public Optional<Integer> checkpointIntervalInMinutes = Optional.empty();
	
	/**
	 * Depth limit on traces in simulation mode.
	 */
	public Optional<Integer> simulationTraceDepthLimit = Optional.empty();
	
	/**
	 * Seed for random simulation.
	 */
	public Optional<Long> seed = Optional.empty();
	
	/**
	 * Adjust seed for random simulation.
	 */
	public Optional<Long> aril = Optional.empty();
	
	/**
	 * Size of largest set which TLC will enumerate.
	 */
	public Optional<Integer> maxSetSize = Optional.empty();
	
	/**
	 * ID of checkpoint from which to recover.
	 */
	public Optional<String> recoveryId = Optional.empty();
	
	/**
	 * Path to metadata directory.
	 */
	public Optional<String> metadataDirectoryPath = Optional.empty();
	
	/**
	 * Path to file to which to log user output (print statements, etc.)
	 */
	public Optional<String> userOutputFilePath = Optional.empty();
	
	/**
	 * Options controlling number of TLC worker threads.
	 */
	public Optional<TlcWorkerThreadControls> tlcWorkerThreadOptions = Optional.empty();
	
	/**
	 * Controls starting depth for depth-first iterative deepening.
	 */
	public Optional<Integer> dfidStartingDepth = Optional.empty();
	
	/**
	 * Controls which irreducible polynomial to use from the list stored in the class FP64.
	 */
	public Optional<Integer> fingerprintFunctionIndex = Optional.empty();

	/**
	 * Percentage of physical computer memory to commit to fingerprint set.
	 */
	public Optional<Double> fingerprintSetMemoryUsePercentage = Optional.empty();
	
	/**
	 * Used for creating nested fingerprint sets.
	 */
	public Optional<Integer> fingerprintBits = Optional.empty();
	
	/**
	 * Path to main TLA+ spec file.
	 */
	public Optional<String> mainSpecFilePath = Optional.empty();
	
	/**
	 * Attempts to parse the command line arguments.
	 * @param args The command line arguments.
	 * @return Either the parsed options or a failure message.
	 */
	public static ParseResult parse(String[] args)
	{
		CommandLineOptions options = new CommandLineOptions();
		int index = 0;
		while (index < args.length)
		{
			if (args[index].equals("-simulate"))
			{
				index++;
				options.simulationModeFlag = true;
				
				// Simulation args can be:
				// file=/path/to/file,num=4711 or num=4711,file=/path/to/file or num=4711 or
				// file=/path/to/file
				// "file=..." and "num=..." are only relevant for simulation which is why they
				// are args to "-simulate".
				if (((index + 1) < args.length) && (args[index].contains("file=") || args[index].contains("num="))) {
					final String[] simArgs = args[index].split(",");
					index++; // consume simulate args
					for (String arg : simArgs) {
						if (arg.startsWith("num=")) {
							options.simulationBehaviorCountLimit =
									Optional.of(Long.parseLong(arg.replace("num=", "")));
						} else if (arg.startsWith("file=")) {
							options.simulationTraceFile =
									Optional.of(arg.replace("file=", ""));
						}
					}
				}
			} else if (args[index].equals("-modelcheck"))
			{
				index++;
				options.modelCheckFlag = true;
			} else if (args[index].equals("-difftrace"))
			{
				index++;
				options.onlyPrintStateTraceDiffsFlag = true;
			} else if (args[index].equals("-deadlock"))
			{
				index++;
				// Confusingly the -deadlock flag specifies *not* checking for deadlock.
				options.doNotCheckDeadlockFlag = true;
			} else if (args[index].equals("-cleanup"))
			{
				index++;
				options.cleanStatesDirectoryFlag = true;
			} else if (args[index].equals("-nowarning"))
			{
				index++;
				options.doNotPrintWarningsFlag = true;
			} else if (args[index].equals("-gzip"))
			{
				index++;
				options.useGZipFlag = true;
			} else if (args[index].equals("-terse"))
			{
				index++;
				options.terseOutputFlag = true;
			} else if (args[index].equals("-continue"))
			{
				index++;
				options.continueAfterInvariantViolationFlag = true;
			} else if (args[index].equals("-view"))
			{
				index++;
				options.useViewFlag = true;
			} else if (args[index].equals("-debug"))
			{
				index++;
				options.debugFlag = true;
			} else if (args[index].equals("-tool"))
			{
				index++;
				options.useToolOutputFormatFlag = true;
			} else if (args[index].equals("-generateSpecTE"))
			{
				index++;
				options.generateErrorTraceSpecFlag = true;
				
				if ((index < args.length) && args[index].equals("nomonolith")) {
					index++;
					options.noMonolithErrorTraceSpecFlag = true;
				}

			} else if (args[index].equals("-help") || args[index].equals("-h"))
			{
				index++;
				// Immediately halt parsing and return if help flag detected
				return ParseResult.helpRequest();
			} else if (args[index].equals("-lncheck"))
			{
				index++;
				if (index < args.length)
				{
					options.livenessCheck = Optional.of(args[index]);
					index++;
				} else
				{
					return ParseResult.failure(
							"Error: expect a strategy such as final for -lncheck option.");
				}
			} else if (args[index].equals("-config"))
			{
				index++;
				if (index < args.length)
				{
					options.configurationFilePath = Optional.of(args[index]);
					index++;
				} else
				{
					return ParseResult.failure(
							"Error: expect a file name for -config option.");
				}
			} else if (args[index].equals("-dump"))
			{
				index++; // consume "-dump".
				if (((index + 1) < args.length) && args[index].startsWith("dot"))
				{
					final String dotArgs = args[index].toLowerCase();
					index++; // consume "dot...".

					DumpFileControls controls = new DumpFileControls(
							dotArgs.contains("colorize"),
							dotArgs.contains("actionlabels"),
							dotArgs.contains("snapshot"));
					options.dumpFileOptions = Optional.of(controls);

					options.dumpFilePath = Optional.of(args[index]);
					index++;
				} else if (index < args.length)
				{
					options.dumpFilePath = Optional.of(args[index]);
					index++;
				} else
				{
					return ParseResult.failure(
							"Error: A file name for dumping states required.");
				}
			} else if (args[index].equals("-coverage"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                    	final int interval = Integer.parseInt(args[index]);
                    	options.coverageIntervalInMinutes = Optional.of(interval);
                        index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.failure(
                        		"Error: An integer for coverage report interval required; encountered: " + args[index]);
                    }
                } else
                {
                    return ParseResult.failure(
                    		"Error: coverage report interval required.");
                }
            } else if (args[index].equals("-checkpoint"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                    	final int interval = Integer.parseInt(args[index]);
                    	options.checkpointIntervalInMinutes = Optional.of(interval);
                        index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.failure(
                        		"Error: An integer for checkpoint interval is required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.failure(
                    		"Error: checkpoint interval required.");
                }
            } else if (args[index].equals("-depth"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                    	final int traceDepth = Integer.parseInt(args[index]);
                    	options.simulationTraceDepthLimit = Optional.of(traceDepth);
                        index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.failure(
                        		"Error: An integer for trace depth required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.failure(
                    		"Error: trace depth required.");
                }
            } else if (args[index].equals("-seed"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                    	final Long seed = Long.parseLong(args[index]);
                        options.seed = Optional.of(seed);
                        index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.failure(
                        		"Error: An integer for seed required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.failure(
                    		"Error: seed required.");
                }
            } else if (args[index].equals("-aril"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                    	final Long aril = Long.parseLong(args[index]);
                        options.aril = Optional.of(aril);
                        index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.failure(
                        		"Error: An integer for aril required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.failure(
                    		"Error: aril required.");
                }
            } else if (args[index].equals("-maxSetSize"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                        final int bound = Integer.parseInt(args[index]);
                        options.maxSetSize = Optional.of(bound);
                    	index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.failure("Error: An integer for maxSetSize required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.failure("Error: maxSetSize required.");
                }
            } else if (args[index].equals("-recover"))
            {
                index++;
                if (index < args.length)
                {
                    options.recoveryId = Optional.of(args[index]);
                    index++;
                } else
                {
                    return ParseResult.failure(
                    		"Error: need to specify the metadata directory for recovery.");
                }
            } else if (args[index].equals("-metadir"))
            {
                index++;
                if (index < args.length)
                {
                    options.metadataDirectoryPath = Optional.of(args[index]);
                    index++;
                } else
                {
                    return ParseResult.failure(
                    		"Error: need to specify the metadata directory (metadir).");
                }
            } else if (args[index].equals("-userFile"))
            {
                index++;
                if (index < args.length)
                {
                	options.userOutputFilePath = Optional.of(args[index]);
                	index++;
                } else
                {
                    return ParseResult.failure(
                    		"Error: need to specify the full qualified userFile.");
                }
            } else if (args[index].equals("-workers"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
						final String token = args[index];
						options.tlcWorkerThreadOptions =
								token.trim().toLowerCase().equals("auto")
								? Optional.of(TlcWorkerThreadControls.auto())
								: Optional.of(TlcWorkerThreadControls.manual(Integer.parseInt(token)));
						index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.failure(
                        		"Error: number of workers or 'auto' required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.failure(
                    		"Error: expect an integer or 'auto' for -workers option.");
                }
            } else if (args[index].equals("-dfid"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                    	final int value = Integer.parseInt(args[index]);
                    	options.dfidStartingDepth = Optional.of(value);
                    	index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.failure(
                        		"Error: expect a nonnegative integer for -dfid option; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.failure(
                    		"Error: expect a nonnegative integer for -dfid option.");
                }
            } else if (args[index].equals("-fp"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                    	final int value = Integer.parseInt(args[index]);
                    	options.fingerprintFunctionIndex = Optional.of(value);
                        index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.failure(
                        		"Error: A number for -fp is required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.failure("Error: expect an integer for -fp option.");
                }
            } else if (args[index].equals("-fpmem"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                        final double value = Double.parseDouble(args[index]);
                        options.fingerprintSetMemoryUsePercentage = Optional.of(value);
                        index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.failure(
                        		"Error: An positive integer or a fraction for fpset memory size/percentage required (-fpmem); encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.failure(
                    		"Error: fpset memory size required for -fpmem.");
                }
            } else if (args[index].equals("-fpbits"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                    	final int value = Integer.parseInt(args[index]);
                    	options.fingerprintBits = Optional.of(value);
                        index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.failure(
                        		"Error: An integer for fpbits required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.failure(
                    		"Error: fpbits required.");
                }
            } else
            {
            	if (args[index].charAt(0) == '-')
                {
                    return ParseResult.failure(
                    		"Error: unrecognized option: " + args[index]);
                }

                if (options.mainSpecFilePath.isPresent())
                {
                	final String value = options.mainSpecFilePath.get();
                    return ParseResult.failure(
                    		"Error: more than one input files: " + value + " and " + args[index]);
                }

                options.mainSpecFilePath = Optional.of(args[index]);
                index++;
            }
		}
		
		return ParseResult.success(options);
	}
	
	/**
	 * Validates provided options are within acceptable hard-coded bounds.
	 * @param options The options to validate.
	 * @return Whether the options passed validation.
	 */
	public static ValidationResult validate(CommandLineOptions options)
	{
		try
		{
			// Ensure coverage interval is a non-negative integer
			options.coverageIntervalInMinutes.ifPresent((value) ->
			{
				if (value < 0)
				{
					throw new IllegalArgumentException(
							"Error: expect a nonnegative integer for -coverage option.");
				}
			});

			// Ensure checkpoint interval is a non-negative integer
			options.checkpointIntervalInMinutes.ifPresent((value) ->
			{
				if (value < 0)
				{
					throw new IllegalArgumentException(
							"Error: expect a nonnegative integer for -checkpoint option.");
				}
			});
		
			// Ensures DFID max is non-negative integer
			options.dfidStartingDepth.ifPresent((value) ->
			{
				if (value < 0)
				{
					throw new IllegalArgumentException(
							"Error: expect a nonnegative integer for -dfid option.");
				}
			});
		
			// Ensures fingerprint set memory ratio is non-negative
			options.fingerprintSetMemoryUsePercentage.ifPresent((value) ->
			{
				if (value < 0)
				{
					throw new IllegalArgumentException(
							"Error: An positive integer or a fraction for fpset memory size/percentage required; encountered " + value);
				}
			});
		
			// Ensures maximum set size is within required range
			options.maxSetSize.ifPresent((value) ->
			{
				final int lowerBound = 1;
				final int upperBound = Integer.MAX_VALUE;
				if (value < lowerBound)
				{
					throw new IllegalArgumentException(
							String.format(
									"Error: Value in interval [{0}, {1}] for maxSetSize required; encountered {2}",
									lowerBound,
									upperBound,
									value));
				}
			});
		
			// Ensures fingerprint function index is within range
			options.fingerprintFunctionIndex.ifPresent((value) ->
			{
				final int lowerBound = 0;
				final int upperBound = FP64.Polys.length - 1;
				if (value < lowerBound || value > upperBound)
				{
					throw new IllegalArgumentException(
							String.format(
									"Error: The number for -fp must be between {0} and {1} (inclusive).",
									lowerBound,
									upperBound));
				}
			});
		
			// Ensures fingerprint bits setting is within range
			options.fingerprintBits.ifPresent((value) ->
			{
				final int lowerBound = 0;
				final int upperBound = MultiFPSet.MAX_FPBITS;
				if (value < lowerBound || value > upperBound)
				{
					throw new IllegalArgumentException(
							String.format(
									"Error: Value in interval [{0}, {1}] for fpbits required; encountered {2}",
									lowerBound,
									upperBound,
									value));
				}
			});
		}
		catch (IllegalArgumentException e)
		{
			return ValidationResult.failure(e.getMessage());
		}
		
		return ValidationResult.success();
	}
	
	/**
	 * Performs transformations on the given options.
	 * @param options The options on which to perform transformations.
	 */
	public static void transform(CommandLineOptions options)
	{
		// Convert liveness check parameter to lower case
		options.livenessCheck = options.livenessCheck.map((String val) -> val.toLowerCase());
		
		// Trim file extension from configuration file path
		options.configurationFilePath = options.configurationFilePath.map(
				(String path) -> path.endsWith(TLAConstants.Files.CONFIG_EXTENSION)
					? path.substring(0, (path.length() - TLAConstants.Files.CONFIG_EXTENSION.length()))
					: path
		);
		
		// Append .dump or .dot to dump file name
		options.dumpFilePath = options.dumpFileOptions.isPresent()
				?  options.dumpFilePath.map(
						(String path) -> path.endsWith(".dot") ? path : path + ".dot")
				:  options.dumpFilePath.map(
						(String path) -> path.endsWith(".dump") ? path : path + ".dump");

		// Appends system-dependent separator to recovery option
		options.recoveryId = options.recoveryId.map((String path) -> path + FileUtil.separator);

		// Appends system-dependent separator to metadata directory option
		options.metadataDirectoryPath = options.metadataDirectoryPath.map(
				(String path) -> path + FileUtil.separator);
		
		// Removes .tla extension from main TLA+ spec
		options.mainSpecFilePath = options.mainSpecFilePath.map(
				(String path) -> path.endsWith(TLAConstants.Files.TLA_EXTENSION)
					? path.substring(0, (path.length() - TLAConstants.Files.TLA_EXTENSION.length()))
					: path
		);
	}
	
	/**
	 * Encapsulates settings related to dump files.
	 * This would be best written as a Java record once that feature is main-lined.
	 */
	public static class DumpFileControls
	{
		public boolean colorize;
		
		public boolean actionLabels;
		
		public boolean snapshot;
		
		public DumpFileControls(boolean colorize, boolean actionLabels, boolean snapshot)
		{
			this.colorize = colorize;
			this.actionLabels = actionLabels;
			this.snapshot = snapshot;
		}
	}
	
	/**
	 * Encapsulates settings related to TLC worker threads.
	 * This should be broken up into different classes once pattern matching is main-lined.
	 */
	public static class TlcWorkerThreadControls
	{
		/**
		 * Set the number of threads to the number available on this machine.
		 */
		public boolean automatic;
		
		/**
		 * Number of threads to use, if explicitly specified.
		 */
		public Optional<Integer> threadCount;
		
		/**
		 * Constructs an instance specifying automatic thread count setting.
		 * @return A new TlcWorkerThreadControls instance.
		 */
		public static TlcWorkerThreadControls auto()
		{
			TlcWorkerThreadControls controls = new TlcWorkerThreadControls();
			controls.automatic = true;
			controls.threadCount = Optional.empty();
			return controls;
		}
		
		/**
		 * Constructs an instance specifying manual thread count setting.
		 * @param threadCount The number of threads to use.
		 * @return A new TlcWorkerThreadControls instance.
		 */
		public static TlcWorkerThreadControls manual(int threadCount)
		{
			TlcWorkerThreadControls controls = new TlcWorkerThreadControls();
			controls.automatic = false;
			controls.threadCount = Optional.of(threadCount);
			return controls;
		}
	}
	
	/**
	 * The result of validating the command line arguments.
	 * This should be broken up into different classes once pattern matching is main-lined.
	 */
	public static class ValidationResult
	{
		/**
		 * Whether the validation succeeded.
		 */
		public boolean success;
		
		/**
		 * The error message, in case of validation failure.
		 */
		public Optional<String> errorMessage;
		
		/**
		 * Creates a validation report in case of success.
		 * @return A successful validation report.
		 */
		public static ValidationResult success()
		{
			ValidationResult result = new ValidationResult();
			result.success = true;
			result.errorMessage = Optional.empty();
			return result;
		}
		
		/**
		 * Creates a validation report in case of failure.
		 * @param errorMessage Message to attach to report.
		 * @return A failed validation report.
		 */
		public static ValidationResult failure(String errorMessage)
		{
			ValidationResult result = new ValidationResult();
			result.success = false;
			result.errorMessage = Optional.of(errorMessage);
			return result;
		}
	}
	
	/**
	 * The result of parsing the command line arguments.
	 * This should be broken up into different classes once pattern matching is main-lined.
	 */
	public static class ParseResult
	{
		/**
		 * Whether the parsing succeeded.
		 */
		public boolean success;
		
		/**
		 * Whether user requested to print help text.
		 */
		public boolean helpRequest;
		
		/**
		 * The parsed command line options, if successful.
		 */
		public Optional<CommandLineOptions> options;
		
		/**
		 * The error message, in case of parse failure.
		 */
		public Optional<String> errorMessage;
		
		/**
		 * Creates a parse report in case of success.
		 * @param options The parse command line options.
		 * @return A successful parser report.
		 */
		public static ParseResult success(CommandLineOptions options)
		{
			ParseResult result = new ParseResult();
			result.success = true;
			result.helpRequest = false;
			result.options = Optional.of(options);
			result.errorMessage = Optional.empty();
			return result;
		}
		
		/**
		 * Creates a parse result in case user requests help text.
		 * @return A help text parser report.
		 */
		public static ParseResult helpRequest()
		{
			ParseResult result = new ParseResult();
			result.success = true;
			result.helpRequest = true;
			result.options = Optional.empty();
			result.errorMessage = Optional.empty();
			return result;
		}
		
		/**
		 * Creates a parse report in case of failure.
		 * @param errorMessage The parse error message.
		 * @return A failed parser report.
		 */
		public static ParseResult failure(String errorMessage)
		{
			ParseResult result = new ParseResult();
			result.success = false;
			result.helpRequest = false;
			result.options = Optional.empty();
			result.errorMessage = Optional.of(errorMessage);
			return result;
		}
	}
}