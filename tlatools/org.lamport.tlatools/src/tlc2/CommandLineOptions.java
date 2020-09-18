package tlc2;

import java.util.Optional;
import util.FileUtil;
import util.TLAConstants;

/**
 * Parses command line options.
 * Future work should examine using a command line parsing library.
 * 
 * Instructions for adding a new command line option:
 *  1. Add a field to this class (encapsulating type with Optional)
 *  2. Add parsing logic to the Parse method
 *  3. Add tests for your new command line option
 * 
 * Try to keep the Parse method focused on content-unaware parsing, not validation.
 * For example, if your option requires an integer in a certain range, this constraint
 * should not be checked & enforced during the parsing process. The old method mixed
 * the three stages (parsing, validation, use) together and the result was an enormous
 * unmaintainable, untestable confusing mess. It is best to keep these separate. It
 * is also best to avoid processing, interpreting, or transforming the user input.
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
	public Optional<Boolean> DoNotCheckDeadlock = Optional.empty();
	
	/**
	 * Cleans up the state directory.
	 */
	public Optional<Boolean> CleanStateDirectory = Optional.empty();
	
	/**
	 * Whether to print warnings.
	 */
	public Optional<Boolean> DoNotPrintWarnings = Optional.empty();
	
	/**
	 * Whether to apply GZip to input/output stream.
	 */
	public Optional<Boolean> UseGZip = Optional.empty();
	
	/**
	 * Whether to expand values in print statements.
	 */
	public Optional<Boolean> TerseOutput = Optional.empty();
	
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
	 * Whether to print the help text.
	 */
	public Optional<Boolean> PrintHelpText = Optional.empty();
	
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
				options.DoNotCheckDeadlock = Optional.of(true);
			} else if (args[index].equals("-cleanup"))
			{
				index++;
				options.CleanStateDirectory = Optional.of(true);
			} else if (args[index].equals("-nowarning"))
			{
				index++;
				options.DoNotPrintWarnings = Optional.of(true);
			} else if (args[index].equals("-gzip"))
			{
				index++;
				options.UseGZip = Optional.of(true);
			} else if (args[index].equals("-terse"))
			{
				index++;
				options.TerseOutput = Optional.of(true);
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
				options.PrintHelpText = Optional.of(true);
			} else if (args[index].equals("-lncheck"))
			{
				index++;
				if (index < args.length)
				{
					index++;
					options.LivenessCheck = Optional.of(args[index].toLowerCase());
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
					String configFilePath = args[index];
					if (configFilePath.endsWith(TLAConstants.Files.CONFIG_EXTENSION))
					{
						configFilePath = configFilePath.substring(0,
								(configFilePath.length() - TLAConstants.Files.CONFIG_EXTENSION.length()));
					}

					index++;
					options.ConfigurationFilePath = Optional.of(configFilePath);
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
					String name = args[index];
					options.DumpFilePath = Optional.of(name.endsWith(".dot") ? name : name + ".dot");
					index++;
				} else if (index < args.length)
				{
					String name = args[index];
					options.DumpFilePath = Optional.of(name.endsWith(".dump") ? name : name + ".dump");
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
                        		"Error: An integer for trace length required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.ParseFailure(
                    		"Error: trace length required.");
                }
            } else if (args[index].equals("-seed"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                        options.Seed = Optional.of(Long.parseLong(args[index]));
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
                        options.Aril = Optional.of(Long.parseLong(args[index]));
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
                    options.RecoveryId = Optional.of(args[index] + FileUtil.separator);
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
                    options.MetadataDirectoryPath = Optional.of(args[index] + FileUtil.separator);
                    index++;
                } else
                {
                    return ParseResult.ParseFailure(
                    		"Error: need to specify the metadata directory.");
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
                    		"Error: need to specify the full qualified user file.");
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
                        		"Error: worker number or 'auto' required. But encountered " + args[index]);
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
                        		"Error: An positive integer or a fraction for fpset memory size/percentage required; encountered " + args[index]);
                    }
                } else
                {
                    return ParseResult.ParseFailure(
                    		"Error: fpset memory size required.");
                }
            } else if (args[index].equals("-fpbits"))
            {
                index++;
                if (index < args.length)
                {
                    try
                    {
                    	final int value = Integer.parseInt(args[index]);
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
			result.Options = Optional.of(options);
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
			result.Options = Optional.empty();
			result.ErrorMessage = Optional.of(errorMessage);
			return result;
		}
	}
}