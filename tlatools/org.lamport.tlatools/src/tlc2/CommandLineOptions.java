package tlc2;

import java.text.ParseException;
import java.util.Optional;
import java.util.function.Supplier;

import tlc2.tool.fp.MultiFPSet;
import tlc2.util.FP64;
import util.FileUtil;
import util.TLAConstants;
import util.Either;
import util.OneOf;

/**
 * Parses command line options.
 * 
 * Instructions for adding a new command line option:
 *  1. Add a field to this class representing your option
 *  	- Use boolean for flags
 *  	- Use Optional<T> for parameters with a single value type
 *  	- Use Optional<Either<L,R>> for parameters with two possible value types
 *  	- Use Optional<OneOf<T1,T2,T3>> for parameters with three possible value types
 *  	- Write your own OneOf implementation if you need more possible value types
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
	 * Whether to generate a specification to re-execute any encountered error trace.
	 */
	public boolean generateErrorTraceSpecFlag = false;
	
	/**
	 * Whether to create a monolithic error trace spec.
	 */
	public boolean noMonolithErrorTraceSpecFlag = false;
	
	/**
	 * Whether to perform liveness checking.
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
	public Optional<DumpFileOptions> dumpFileOptions = Optional.empty();
	
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
	public Optional<Either<AutomaticallySetTlcWorkerThreadCount, ManuallySetTlcWorkerThreadCount>> tlcWorkerThreadOptions =
			Optional.empty();
	
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
	 * @return Either the parsed options, a print help request, or a failure message.
	 */
	public static OneOf<FailedParseResult, HelpRequestParseResult, SuccessfulParseResult> parse(String[] args)
	{
		CommandLineOptions options = new CommandLineOptions();
		try
		{
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
					HelpRequestParseResult result = new HelpRequestParseResult();
					return OneOf.second(result);
				} else if (args[index].equals("-lncheck"))
				{
					index++;
					if (index < args.length)
					{
						options.livenessCheck = Optional.of(args[index]);
						index++;
					} else
					{
						throw new ParseException(
								"Error: expect a strategy such as final for -lncheck option.",
								index);
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
						throw new ParseException(
								"Error: expect a file name for -config option.",
								index);
					}
				} else if (args[index].equals("-dump"))
				{
					index++; // consume "-dump".
					if (((index + 1) < args.length) && args[index].startsWith("dot"))
					{
						final String dotArgs = args[index].toLowerCase();
						index++; // consume "dot...".

						DumpFileOptions controls = new DumpFileOptions(
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
						throw new ParseException(
								"Error: A file name for dumping states required.",
								index);
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
							throw new ParseException(
									"Error: An integer for coverage report interval required; encountered: " + args[index],
									index);
						}
					} else
					{
						throw new ParseException(
								"Error: coverage report interval required.",
								index);
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
							throw new ParseException(
									"Error: An integer for checkpoint interval is required; encountered " + args[index],
									index);
						}
					} else
					{
						throw new ParseException(
								"Error: checkpoint interval required.",
								index);
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
							throw new ParseException(
									"Error: An integer for trace depth required; encountered " + args[index],
									index);
						}
					} else
					{
						throw new ParseException(
								"Error: trace depth required.",
								index);
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
							throw new ParseException(
									"Error: An integer for seed required; encountered " + args[index],
									index);
						}
					} else
					{
						throw new ParseException("Error: seed required.", index);
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
							throw new ParseException(
									"Error: An integer for aril required; encountered " + args[index],
									index);
						}
					} else
					{
						throw new ParseException("Error: aril required.", index);
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
							throw new ParseException(
									"Error: An integer for maxSetSize required; encountered " + args[index],
									index);
						}
					} else
					{
						throw new ParseException("Error: maxSetSize required.", index);
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
						throw new ParseException(
								"Error: need to specify the metadata directory for recovery.",
								index);
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
						throw new ParseException(
								"Error: need to specify the metadata directory (metadir).",
								index);
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
						throw new ParseException(
								"Error: need to specify the full qualified userFile.",
								index);
					}
				} else if (args[index].equals("-workers"))
				{
					index++;
					if (index < args.length)
					{
						try
						{
							final String token = args[index];
							Either<AutomaticallySetTlcWorkerThreadCount, ManuallySetTlcWorkerThreadCount> workerOption =
									token.trim().toLowerCase().equals("auto")
									? Either.left(new AutomaticallySetTlcWorkerThreadCount())
									: Either.right(new ManuallySetTlcWorkerThreadCount(Integer.parseInt(token)));
							options.tlcWorkerThreadOptions = Optional.of(workerOption);
							index++;
						} catch (NumberFormatException e)
						{
							throw new ParseException(
									"Error: number of workers or 'auto' required; encountered " + args[index],
									index);
						}
					} else
					{
						throw new ParseException(
								"Error: expect an integer or 'auto' for -workers option.",
								index);
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
							throw new ParseException(
									"Error: expect a nonnegative integer for -dfid option; encountered " + args[index],
									index);
						}
					} else
					{
						throw new ParseException(
								"Error: expect a nonnegative integer for -dfid option.",
								index);
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
							throw new ParseException(
									"Error: A number for -fp is required; encountered " + args[index],
									index);
						}
					} else
					{
						throw new ParseException("Error: expect an integer for -fp option.", index);
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
							throw new ParseException(
									"Error: An positive integer or a fraction for fpset memory size/percentage required (-fpmem); encountered " + args[index],
									index);
						}
					} else
					{
						throw new ParseException(
								"Error: fpset memory size required for -fpmem.",
								index);
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
							throw new ParseException(
									"Error: An integer for fpbits required; encountered " + args[index],
									index);
						}
					} else
					{
						throw new ParseException("Error: fpbits required.", index);
					}
				} else
				{
					if (args[index].charAt(0) == '-')
					{
						throw new ParseException("Error: unrecognized option: " + args[index], index);
					}

					if (options.mainSpecFilePath.isPresent())
					{
						final String value = options.mainSpecFilePath.get();
						throw new ParseException(
								"Error: more than one input files: " + value + " and " + args[index],
								index);
					}

					options.mainSpecFilePath = Optional.of(args[index]);
					index++;
				}
			}
		} catch (ParseException e)
		{
			FailedParseResult result = new FailedParseResult(e.getMessage(), e.getErrorOffset());
			return OneOf.first(result);
		}
		
		SuccessfulParseResult result = new SuccessfulParseResult(options);
		return OneOf.third(result);
	}
	
	/**
	 * Validates provided options are within acceptable hard-coded bounds.
	 * @param options The options to validate.
	 * @param hostProcessorCount A method returning the number of processors on the host system
	 * @return Whether the options passed validation.
	 */
	public static Either<FailedValidationResult, SuccessfulValidationResult> validate(
			CommandLineOptions options,
			Supplier<Integer> hostProcessorCount)
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
			
			// Ensures at least one TLC worker thread was specified
			options.tlcWorkerThreadOptions.ifPresent(either ->
			{
				either.ifPresent(
					(auto) ->
					{
						final int workerCount = hostProcessorCount.get();
						if (workerCount < 1)
						{
							throw new IllegalArgumentException(
									String.format(
											"Error: auto-detection of host processor count for TLC workers returned [{0}]; require at least 1",
											workerCount));
						}
					},
					(manual) ->
					{
						if (manual.workerThreadCount < 1)
						{
							throw new IllegalArgumentException(
									"Error: require at least 1 TLC worker for -workers option");
						}
					});
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
			FailedValidationResult result = new FailedValidationResult(e.getMessage());
			return Either.left(result);
		}
		
		SuccessfulValidationResult result = new SuccessfulValidationResult();
		return Either.right(result);
	}
	
	/**
	 * Performs transformations on the given options.
	 * @param options The options on which to perform transformations.
	 */
	public void transform()
	{
		// Convert liveness check parameter to lower case
		this.livenessCheck = this.livenessCheck.map((String val) -> val.toLowerCase());
		
		// Trim file extension from configuration file path
		this.configurationFilePath = this.configurationFilePath.map(
				(String path) -> path.endsWith(TLAConstants.Files.CONFIG_EXTENSION)
					? path.substring(0, (path.length() - TLAConstants.Files.CONFIG_EXTENSION.length()))
					: path
		);
		
		// Append .dump or .dot to dump file name
		this.dumpFilePath = this.dumpFileOptions.isPresent()
				?  this.dumpFilePath.map(
						(String path) -> path.endsWith(".dot") ? path : path + ".dot")
				:  this.dumpFilePath.map(
						(String path) -> path.endsWith(".dump") ? path : path + ".dump");

		// Appends system-dependent separator to recovery option
		this.recoveryId = this.recoveryId.map((String path) -> path + FileUtil.separator);

		// Appends system-dependent separator to metadata directory option
		this.metadataDirectoryPath = this.metadataDirectoryPath.map(
				(String path) -> path + FileUtil.separator);
		
		// Removes .tla extension from main TLA+ spec
		this.mainSpecFilePath = this.mainSpecFilePath.map(
				(String path) -> path.endsWith(TLAConstants.Files.TLA_EXTENSION)
					? path.substring(0, (path.length() - TLAConstants.Files.TLA_EXTENSION.length()))
					: path
		);
	}
	
	/**
	 * Represents the option to automatically set number of TLC worker threads.
	 * Should be rewritten as a record once that feature is main-lined.
	 */
	public static class AutomaticallySetTlcWorkerThreadCount { }
	
	/**
	 * Represents the option to manually set number of TLC worker threads.
	 */
	public static class ManuallySetTlcWorkerThreadCount
	{
		/**
		 * The number of worker threads TLC should use.
		 */
		public int workerThreadCount;
		
		/**
		 * Creates a new ManuallySetTlcWorkerThreadCount instance.
		 * @param workerThreadCount The number of worker threads TLC should use.
		 */
		public ManuallySetTlcWorkerThreadCount(int workerThreadCount)
		{
			this.workerThreadCount = workerThreadCount;
		}
	}
	
	/**
	 * Represents a successful command line options validation result.
	 */
	public static class SuccessfulValidationResult { }
	
	/**
	 * Represents a failed command line options validation result.
	 * Should be rewritten as a record once that feature is main-lined.
	 */
	public static class FailedValidationResult
	{
		/**
		 * The human-readable error message.
		 */
		public String errorMessage;
		
		/**
		 * Creates a new FailedValidationResult
		 * @param errorMessage The human-readable error message.
		 */
		public FailedValidationResult(String errorMessage)
		{
			this.errorMessage = errorMessage;
		}
	}
	
	/**
	 * Represents a successful parse result.
	 * Should be rewritten as a record once that feature is main-lined.
	 */
	public static class SuccessfulParseResult
	{
		/**
		 * The parsed command line options.
		 */
		public CommandLineOptions options;
		
		/**
		 * Creates a new SuccessfulParseResult instance.
		 * @param options The parsed command line options.
		 */
		public SuccessfulParseResult(CommandLineOptions options)
		{
			this.options = options;
		}
	}
	
	/**
	 * Represents a request to print command line option help.
	 */
	public static class HelpRequestParseResult { }
	
	/**
	 * Represents a failed parse result.
	 * Should be rewritten as a record once that feature is main-lined.
	 */
	public static class FailedParseResult
	{
		/**
		 * The human-readable error message.
		 */
		public String errorMessage;
		
		/**
		 * The index in the args array where parsing failed.
		 */
		public int index;
		
		/**
		 * Creates a new FailedParseResult instance.
		 * @param errorMessage The human-readable error message.
		 * @param index The index in the args array where parsing failed.
		 */
		public FailedParseResult(String errorMessage, int index)
		{
			this.errorMessage = errorMessage;
			this.index = index;
		}
	}
}
