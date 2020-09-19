package tlc2;

import java.util.Optional;
import util.FileUtil;
import util.TLAConstants;

/**
 * Parses command line options.
 * 
 * Instructions for adding a new command line option:
 *  1. Add a field to this class (encapsulating type with Optional)
 *  2. Add parsing logic to the Parse method
 *  3. Add validation logic to the Validate method (if required)
 *  4. Add transformation logic to the Transform method (if required)
 *  5. Add tests for your new option for all of those methods
 *  6. Add text describing your option to the help output
 * 
 * Try to keep the Parse method focused on content-unaware parsing, not validation.
 * For example, if your option requires an integer in a certain range, this constraint
 * should not be checked & enforced during the parsing process. The old method mixed
 * the three stages (parsing, validation, use) together and the result was an enormous
 * unmaintainable, untestable confusing mess. It is best to keep these separate. It
 * is also best to avoid processing, interpreting, or transforming the user input.
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
	public Optional<Boolean> SimulationMode = Optional.empty();
	
	/**
	 * The maximum number of traces/behaviors to generate in simulation mode.
	 */
	public Optional<Long> SimulationBehaviorCountLimit = Optional.empty();
	
	/**
	 * File to which to write simulation traces.
	 */
	public Optional<String> SimulationTraceFile = Optional.empty();
	
	/**
	 * Whether to model check the spec (ignored).
	 */
	public Optional<Boolean> ModelCheck = Optional.empty();
	
	/**
	 * Whether to only print state differences in traces.
	 */
	public Optional<Boolean> OnlyPrintStateTraceDiffs = Optional.empty();
	
	/**
	 * Whether to check for deadlock.
	 */
	public Optional<Boolean> CheckDeadlock = Optional.empty();
	
	/**
	 * Whether to clean states directory.
	 */
	public Optional<Boolean> CleanStatesDirectory = Optional.empty();
	
	/**
	 * Whether to print warnings.
	 */
	public Optional<Boolean> PrintWarnings = Optional.empty();
	
	/**
	 * Whether to apply GZip to input/output stream.
	 */
	public Optional<Boolean> UseGZip = Optional.empty();
	
	/**
	 * Whether to expand values in print statements.
	 */
	public Optional<Boolean> ExpandValuesInPrintStatements = Optional.empty();
	
	/**
	 * Whether to continue running after an invariant is violated.
	 */
	public Optional<Boolean> ContinueAfterInvariantViolation = Optional.empty();
	
	/**
	 * Whether to apply a VIEW when printing out states.
	 */
	public Optional<Boolean> UseView = Optional.empty();
	
	/**
	 * Whether to print debugging information.
	 */
	public Optional<Boolean> Debug = Optional.empty();
	
	/**
	 * Whether to output messages in an easily-parsed format.
	 */
	public Optional<Boolean> UseToolOutputFormat = Optional.empty();
	
	/**
	 * Whether to generate a spec to re-execute any encountered error trace.
	 */
	public Optional<Boolean> GenerateErrorTraceSpec = Optional.empty();
	
	/**
	 * Whether to create a monolithic error trace spec.
	 */
	public Optional<Boolean> CreateMonolithErrorTraceSpec = Optional.empty();
	
	/**
	 * TODO: find out what this does.
	 */
	public Optional<String> LivenessCheck = Optional.empty();
	
	/**
	 * Path to the model checking configuration file.
	 */
	public Optional<String> ConfigurationFilePath = Optional.empty();
	
	/**
	 * Path to the state dump file.
	 */
	public Optional<String> DumpFilePath = Optional.empty();
	
	/**
	 * Options controlling how states are dumped to file.
	 */
	public Optional<DumpFileControls> DumpFileOptions = Optional.empty();
	
	/**
	 * Number of minutes between collection of coverage information.
	 */
	public Optional<Integer> CoverageIntervalInMinutes = Optional.empty();
	
	/**
	 * Number of minutes between checkpoints.
	 */
	public Optional<Integer> CheckpointIntervalInMinutes = Optional.empty();
	
	/**
	 * Depth limit on traces in simulation mode.
	 */
	public Optional<Integer> SimulationTraceDepthLimit = Optional.empty();
	
	/**
	 * Seed for random simulation.
	 */
	public Optional<Long> Seed = Optional.empty();
	
	/**
	 * Adjust seed for random simulation.
	 */
	public Optional<Long> Aril = Optional.empty();
	
	/**
	 * Size of largest set which TLC will enumerate.
	 */
	public Optional<Integer> MaxSetSize = Optional.empty();
	
	/**
	 * ID of checkpoint from which to recover.
	 */
	public Optional<String> RecoveryId = Optional.empty();
	
	/**
	 * Path to metadata directory.
	 */
	public Optional<String> MetadataDirectoryPath = Optional.empty();
	
	/**
	 * Path to file to which to log user output (print statements, etc.)
	 */
	public Optional<String> UserOutputFilePath = Optional.empty();
	
	/**
	 * Options controlling number of TLC worker threads.
	 */
	public Optional<TlcWorkerThreadControls> TlcWorkerThreadOptions = Optional.empty();
	
	/**
	 * Controls starting depth for depth-first iterative deepening.
	 */
	public Optional<Integer> DfidStartingDepth = Optional.empty();
	
	/**
	 * Controls which irreducible polynomial to use from the list stored in the class FP64.
	 */
	public Optional<Integer> FingerprintFunctionIndex = Optional.empty();

	/**
	 * Percentage of physical computer memory to commit to fingerprint set.
	 */
	public Optional<Double> FingerprintSetMemoryUsePercentage = Optional.empty();
	
	/**
	 * Used for creating nested fingerprint sets.
	 */
	public Optional<Integer> FingerprintBits = Optional.empty();
	
	/**
	 * Path to main TLA+ spec file.
	 */
	public Optional<String> MainSpecFilePath = Optional.empty();
	
	/**
	 * Attempts to parse the command line arguments.
	 * @param args The command line arguments.
	 * @return Either the parsed options or a failure message.
	 */
	public static ParseResult Parse(String[] args)
	{
		CommandLineOptions options = new CommandLineOptions();
		int index = 0;
		while (index < args.length)
		{
			if (args[index].equals("-simulate"))
			{
				index++;
				options.SimulationMode = Optional.of(true);
				
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
							options.SimulationBehaviorCountLimit =
									Optional.of(Long.parseLong(arg.replace("num=", "")));
						} else if (arg.startsWith("file=")) {
							options.SimulationTraceFile =
									Optional.of(arg.replace("file=", ""));
						}
					}
				}
			} else if (args[index].equals("-modelcheck"))
			{
				index++;
				options.ModelCheck = Optional.of(true);
			} else if (args[index].equals("-difftrace"))
			{
				index++;
				options.OnlyPrintStateTraceDiffs = Optional.of(true);
			} else if (args[index].equals("-deadlock"))
			{
				index++;
				// Confusingly the -deadlock flag specifies *not* checking for deadlock.
				options.CheckDeadlock = Optional.of(false);
			} else if (args[index].equals("-cleanup"))
			{
				index++;
				options.CleanStatesDirectory = Optional.of(true);
			} else if (args[index].equals("-nowarning"))
			{
				index++;
				options.PrintWarnings = Optional.of(false);
			} else if (args[index].equals("-gzip"))
			{
				index++;
				options.UseGZip = Optional.of(true);
			} else if (args[index].equals("-terse"))
			{
				index++;
				options.ExpandValuesInPrintStatements = Optional.of(false);
			} else if (args[index].equals("-continue"))
			{
				index++;
				options.ContinueAfterInvariantViolation = Optional.of(true);
			} else if (args[index].equals("-view"))
			{
				index++;
				options.UseView = Optional.of(true);
			} else if (args[index].equals("-debug"))
			{
				index++;
				options.Debug = Optional.of(true);
			} else if (args[index].equals("-tool"))
			{
				index++;
				options.UseToolOutputFormat = Optional.of(true);
			} else if (args[index].equals("-generateSpecTE"))
			{
				index++;
				options.GenerateErrorTraceSpec = Optional.of(true);
				
				if ((index < args.length) && args[index].equals("nomonolith")) {
					index++;
					options.CreateMonolithErrorTraceSpec = Optional.of(false);
				} else {
					options.CreateMonolithErrorTraceSpec = Optional.of(true);
				}
			} else if (args[index].equals("-help") || args[index].equals("-h"))
			{
				index++;
				// Immediately halt parsing and return if help flag detected
				return ParseResult.ParseHelpRequest();
			} else if (args[index].equals("-lncheck"))
			{
				index++;
				if (index < args.length)
				{
					options.LivenessCheck = Optional.of(args[index]);
					index++;
				} else
				{
					return ParseResult.ParseFailure(
							"Error: expect a strategy such as final for -lncheck option.");
				}
			} else if (args[index].equals("-config"))
			{
				index++;
				if (index < args.length)
				{
					options.ConfigurationFilePath = Optional.of(args[index]);
					index++;
				} else
				{
					return ParseResult.ParseFailure(
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
					options.DumpFileOptions = Optional.of(controls);

					options.DumpFilePath = Optional.of(args[index]);
					index++;
				} else if (index < args.length)
				{
					options.DumpFilePath = Optional.of(args[index]);
					index++;
				} else
				{
					return ParseResult.ParseFailure(
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
                    	options.CoverageIntervalInMinutes = Optional.of(interval);
                        index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.ParseFailure(
                        		"Error: An integer for coverage report interval required; encountered: " + args[index]);
                    }
                } else
                {
                    return ParseResult.ParseFailure(
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
                    	options.CheckpointIntervalInMinutes = Optional.of(interval);
                        index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.ParseFailure(
                        		"Error: An integer for checkpoint interval is required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.ParseFailure(
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
                    	options.SimulationTraceDepthLimit = Optional.of(traceDepth);
                        index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.ParseFailure(
                        		"Error: An integer for trace depth required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.ParseFailure(
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
                        options.Seed = Optional.of(seed);
                        index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.ParseFailure(
                        		"Error: An integer for seed required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.ParseFailure(
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
                        options.Aril = Optional.of(aril);
                        index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.ParseFailure(
                        		"Error: An integer for aril required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.ParseFailure(
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
                        options.MaxSetSize = Optional.of(bound);
                    	index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.ParseFailure("Error: An integer for maxSetSize required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.ParseFailure("Error: maxSetSize required.");
                }
            } else if (args[index].equals("-recover"))
            {
                index++;
                if (index < args.length)
                {
                    options.RecoveryId = Optional.of(args[index]);
                    index++;
                } else
                {
                    return ParseResult.ParseFailure(
                    		"Error: need to specify the metadata directory for recovery.");
                }
            } else if (args[index].equals("-metadir"))
            {
                index++;
                if (index < args.length)
                {
                    options.MetadataDirectoryPath = Optional.of(args[index]);
                    index++;
                } else
                {
                    return ParseResult.ParseFailure(
                    		"Error: need to specify the metadata directory (metadir).");
                }
            } else if (args[index].equals("-userFile"))
            {
                index++;
                if (index < args.length)
                {
                	options.UserOutputFilePath = Optional.of(args[index]);
                	index++;
                } else
                {
                    return ParseResult.ParseFailure(
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
						options.TlcWorkerThreadOptions =
								token.trim().toLowerCase().equals("auto")
								? Optional.of(TlcWorkerThreadControls.Auto())
								: Optional.of(TlcWorkerThreadControls.Manual(Integer.parseInt(token)));
						index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.ParseFailure(
                        		"Error: number of workers or 'auto' required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.ParseFailure(
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
                    	options.DfidStartingDepth = Optional.of(value);
                    	index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.ParseFailure(
                        		"Error: expect a nonnegative integer for -dfid option; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.ParseFailure(
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
                    	options.FingerprintFunctionIndex = Optional.of(value);
                        index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.ParseFailure(
                        		"Error: A number for -fp is required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.ParseFailure("Error: expect an integer for -fp option.");
                }
            } else if (args[index].equals("-fpmem"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                        final double value = Double.parseDouble(args[index]);
                        options.FingerprintSetMemoryUsePercentage = Optional.of(value);
                        index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.ParseFailure(
                        		"Error: An positive integer or a fraction for fpset memory size/percentage required (-fpmem); encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.ParseFailure(
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
                    	options.FingerprintBits = Optional.of(value);
                        index++;
                    } catch (NumberFormatException e)
                    {
                        return ParseResult.ParseFailure(
                        		"Error: An integer for fpbits required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.ParseFailure(
                    		"Error: fpbits required.");
                }
            } else
            {
            	if (args[index].charAt(0) == '-')
                {
                    return ParseResult.ParseFailure(
                    		"Error: unrecognized option: " + args[index]);
                }

                if (options.MainSpecFilePath.isPresent())
                {
                	final String value = options.MainSpecFilePath.get();
                    return ParseResult.ParseFailure(
                    		"Error: more than one input files: " + value + " and " + args[index]);
                }

                options.MainSpecFilePath = Optional.of(args[index]);
                index++;
            }
		}
		
		return ParseResult.ParseSuccess(options);
	}
	
	public static boolean Validate(CommandLineOptions options)
	{
		// Ensure coverage interval is positive integer
		if (options.CoverageIntervalInMinutes.isPresent())
		{
			int value = options.CoverageIntervalInMinutes.get();
			if (value < 0)
			{
				return false;
			}
		}
		
		return true;
	}
	
	public static void Transform(CommandLineOptions options)
	{
		// Convert liveness check parameter to lower case
		options.LivenessCheck = options.LivenessCheck.map((String val) -> val.toLowerCase());
		
		// Trim file extension from configuration file path
		options.ConfigurationFilePath = options.ConfigurationFilePath.map(
				(String path) -> path.endsWith(TLAConstants.Files.CONFIG_EXTENSION)
					? path.substring(0, (path.length() - TLAConstants.Files.CONFIG_EXTENSION.length()))
					: path
		);
		
		// Append .dump or .dot to dump file name
		options.DumpFilePath = options.DumpFileOptions.isPresent()
				?  options.DumpFilePath.map(
						(String path) -> path.endsWith(".dot") ? path : path + ".dot")
				:  options.DumpFilePath.map(
						(String path) -> path.endsWith(".dump") ? path : path + ".dump");

		// Appends system-dependent separator to recovery option
		options.RecoveryId = options.RecoveryId.map((String path) -> path + FileUtil.separator);

		// Appends system-dependent separator to metadata directory option
		options.MetadataDirectoryPath = options.MetadataDirectoryPath.map(
				(String path) -> path + FileUtil.separator);
	}
	
	/**
	 * Encapsulates settings related to dump files.
	 * This would be best written as a Java record once that feature is out of preview.
	 */
	public static class DumpFileControls
	{
		public boolean Colorize;
		
		public boolean ActionLabels;
		
		public boolean Snapshot;
		
		public DumpFileControls(boolean colorize, boolean actionLabels, boolean snapshot)
		{
			this.Colorize = colorize;
			this.ActionLabels = actionLabels;
			this.Snapshot = snapshot;
		}
	}
	
	/**
	 * Encapsulates settings related to TLC worker threads.
	 * This would be best written as a Java record once that feature is out of preview.
	 */
	public static class TlcWorkerThreadControls
	{
		/**
		 * Set the number of threads to the number available on this machine.
		 */
		public boolean Automatic;
		
		/**
		 * Number of threads to use, if explicitly specified.
		 */
		public Optional<Integer> ThreadCount;
		
		/**
		 * Constructs an instance specifying automatic thread count setting.
		 * @return A new TlcWorkerThreadControls instance.
		 */
		public static TlcWorkerThreadControls Auto()
		{
			TlcWorkerThreadControls controls = new TlcWorkerThreadControls();
			controls.Automatic = true;
			controls.ThreadCount = Optional.empty();
			return controls;
		}
		
		/**
		 * Constructs an instance specifying manual thread count setting.
		 * @param threadCount The number of threads to use.
		 * @return A new TlcWorkerThreadControls instance.
		 */
		public static TlcWorkerThreadControls Manual(int threadCount)
		{
			TlcWorkerThreadControls controls = new TlcWorkerThreadControls();
			controls.Automatic = false;
			controls.ThreadCount = Optional.of(threadCount);
			return controls;
		}
	}
	
	/**
	 * The result of parsing the command line arguments.
	 */
	public static class ParseResult
	{
		/**
		 * Whether the parsing succeeded.
		 */
		public boolean Success;
		
		/**
		 * Whether user requested to print help text.
		 */
		public boolean HelpRequest;
		
		/**
		 * The parsed command line options, if successful.
		 */
		public Optional<CommandLineOptions> Options;
		
		/**
		 * The error message, in case of parse failure.
		 */
		public Optional<String> ErrorMessage;
		
		/**
		 * Creates a parse report in case of success.
		 * @param options The parse command line options.
		 * @return A successful parser report.
		 */
		public static ParseResult ParseSuccess(CommandLineOptions options)
		{
			ParseResult result = new ParseResult();
			result.Success = true;
			result.HelpRequest = false;
			result.Options = Optional.of(options);
			result.ErrorMessage = Optional.empty();
			return result;
		}
		
		/**
		 * Creates a parse result in case user requests help text.
		 * @return A help text parser report.
		 */
		public static ParseResult ParseHelpRequest()
		{
			ParseResult result = new ParseResult();
			result.Success = true;
			result.HelpRequest = true;
			result.Options = Optional.empty();
			result.ErrorMessage = Optional.empty();
			return result;
		}
		
		/**
		 * Creates a parse report in case of failure.
		 * @param errorMessage The parse error message.
		 * @return A failed parser report.
		 */
		public static ParseResult ParseFailure(String errorMessage)
		{
			ParseResult result = new ParseResult();
			result.Success = false;
			result.HelpRequest = false;
			result.Options = Optional.empty();
			result.ErrorMessage = Optional.of(errorMessage);
			return result;
		}
	}
}