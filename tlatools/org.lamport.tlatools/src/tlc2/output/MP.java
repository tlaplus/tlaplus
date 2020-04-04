package tlc2.output;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.io.Writer;
import java.text.DecimalFormat;
import java.text.SimpleDateFormat;
import java.util.Date;

import tlc2.TLCGlobals;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.tool.liveness.LiveWorker;
import tlc2.util.statistics.IBucketStatistics;
import util.Assert;
import util.Assert.TLCRuntimeException;
import util.DebugPrinter;
import util.Set;
import util.TLAConstants;
import util.TLAFlightRecorder;
import util.ToolIO;

/**
 * This class is used in the following way to support the replacements of the
 * strings inside of the code. Any kind of String used as a message reported to the user should be replaced with
 * the call of the message printer.
 * <br><br>
 * The main class for message resolution and printing is called {@link MP}
 * The main class for constants is called {@link EC}
 * <br><br>
 * Here is an example for usage of non-parameterized messages. Assume we have code like this:
 * <code>Assert.fail("getLevel called for TheoremNode before levelCheck");</code>
 * which should be replaced by the call of Assert with the error code. First of all we need to add an additional
 * case in the method {@link MP#getMessage(int, int, String[])}. For doing this, a new constant is required. 
 * Since all constants are in the {@link EC} class we add a line: 
 * <br><br> 
 * <code>public final static int GET_LEVEL_THEOREM_BEFORE_LEVEL_CHECK = 4005;</code>
 * <br><br>
 * After the constant is added we add the case to the switch:
 * <br><br><code> 
 * case EC.GET_LEVEL_THEOREM_BEFORE_LEVEL_CHECK:
 *     b.append("getLevel called for TheoremNode before levelCheck");
 *     break;
 * </code>
 * <br><br> 
 * After that, we replace the code Assert.fail("getLevel called for TheoremNode before levelCheck"); by
 * <code>Assert.fail(EC.GET_LEVEL_THEOREM_BEFORE_LEVEL_CHECK)</code>; There will be a warning inside of the 
 * class, that SANYCodes can not be resolve, so we add it to the imported classes. In order to do this quickly, 
 * put the cursor into the line with the error, and hit <key>Ctrl + 1</key>. The opened quick assist will propose to add the import...
 * Another acceleration can be achieved by adding the case first and pointing the non-existent constant. Again the error 
 * will appear in the MessageResolver class and the <key>Ctrl + 1</key> will open the quick assist first proposition will be to add
 * the constant to the {@link EC}. This saves the typing of the name of the constant and the modifier, but you have to put 
 * the value of the constant...
 * <br><br> 
 * Now assume there is another message in the same class: 
 * <br><br>
 * <code>Assert.fail("getLevel called for LabelNode before levelCheck");</code>
 * <br><br>
 * The message is actually the same, but instead of TheoremNode it has LabelNode. In order to keep with it you can add another
 * constant, or re-think the semantics of the actual message. So in this case I would change the semantics and rename the 
 * constant to GET_LEVEL_BEFORE_LEVEL_CHECK. Change the code in the case to:
 * <br><br>
 * <code>case EC.GET_LEVEL_BEFORE_LEVEL_CHECK:
 *     b.append("getLevel called for %1% before levelCheck");
 *     break;
 * </code>
 * <br><br>
 * Please note the %1% in the string. This will be replaced by the first parameter. The call will be:
 * <code>Assert.fail(EC.GET_LEVEL_BEFORE_LEVEL_CHECK, new String[]{"TheoremNode"});</code> and 
 * <code>Assert.fail(EC.GET_LEVEL_BEFORE_LEVEL_CHECK, new String[]{"LabelNode"});</code> respectively. 
 * <br><br>
 * There is also a shortcut for writing this: <code>Assert.fail(EC.GET_LEVEL_BEFORE_LEVEL_CHECK, "LabelNode");</code> which
 * is a shortcut.
 * <br><br>
 * In general, you can insert more %i% into the message and provide the parameters in the String array.  
 * <br><br>
 *         
 * @author Simon Zambrovski
 * @version $Id$
 */
public class MP
{
	// https://stackoverflow.com/a/45444716/6291195
	public static class Colors {
		// Reset
		public static final String RESET = "\033[0m"; // Text Reset

		// Regular Colors
		public static final String BLACK = "\033[0;30m"; // BLACK
		public static final String RED = "\033[0;31m"; // RED
		public static final String GREEN = "\033[0;32m"; // GREEN
		public static final String YELLOW = "\033[0;33m"; // YELLOW
		public static final String BLUE = "\033[0;34m"; // BLUE
		public static final String PURPLE = "\033[0;35m"; // PURPLE
		public static final String CYAN = "\033[0;36m"; // CYAN
		public static final String WHITE = "\033[0;37m"; // WHITE

		// Bold
		public static final String BLACK_BOLD = "\033[1;30m"; // BLACK
		public static final String RED_BOLD = "\033[1;31m"; // RED
		public static final String GREEN_BOLD = "\033[1;32m"; // GREEN
		public static final String YELLOW_BOLD = "\033[1;33m"; // YELLOW
		public static final String BLUE_BOLD = "\033[1;34m"; // BLUE
		public static final String PURPLE_BOLD = "\033[1;35m"; // PURPLE
		public static final String CYAN_BOLD = "\033[1;36m"; // CYAN
		public static final String WHITE_BOLD = "\033[1;37m"; // WHITE

		// Underline
		public static final String BLACK_UNDERLINED = "\033[4;30m"; // BLACK
		public static final String RED_UNDERLINED = "\033[4;31m"; // RED
		public static final String GREEN_UNDERLINED = "\033[4;32m"; // GREEN
		public static final String YELLOW_UNDERLINED = "\033[4;33m"; // YELLOW
		public static final String BLUE_UNDERLINED = "\033[4;34m"; // BLUE
		public static final String PURPLE_UNDERLINED = "\033[4;35m"; // PURPLE
		public static final String CYAN_UNDERLINED = "\033[4;36m"; // CYAN
		public static final String WHITE_UNDERLINED = "\033[4;37m"; // WHITE

		// Background
		public static final String BLACK_BACKGROUND = "\033[40m"; // BLACK
		public static final String RED_BACKGROUND = "\033[41m"; // RED
		public static final String GREEN_BACKGROUND = "\033[42m"; // GREEN
		public static final String YELLOW_BACKGROUND = "\033[43m"; // YELLOW
		public static final String BLUE_BACKGROUND = "\033[44m"; // BLUE
		public static final String PURPLE_BACKGROUND = "\033[45m"; // PURPLE
		public static final String CYAN_BACKGROUND = "\033[46m"; // CYAN
		public static final String WHITE_BACKGROUND = "\033[47m"; // WHITE

		// High Intensity
		public static final String BLACK_BRIGHT = "\033[0;90m"; // BLACK
		public static final String RED_BRIGHT = "\033[0;91m"; // RED
		public static final String GREEN_BRIGHT = "\033[0;92m"; // GREEN
		public static final String YELLOW_BRIGHT = "\033[0;93m"; // YELLOW
		public static final String BLUE_BRIGHT = "\033[0;94m"; // BLUE
		public static final String PURPLE_BRIGHT = "\033[0;95m"; // PURPLE
		public static final String CYAN_BRIGHT = "\033[0;96m"; // CYAN
		public static final String WHITE_BRIGHT = "\033[0;97m"; // WHITE

		// Bold High Intensity
		public static final String BLACK_BOLD_BRIGHT = "\033[1;90m"; // BLACK
		public static final String RED_BOLD_BRIGHT = "\033[1;91m"; // RED
		public static final String GREEN_BOLD_BRIGHT = "\033[1;92m"; // GREEN
		public static final String YELLOW_BOLD_BRIGHT = "\033[1;93m";// YELLOW
		public static final String BLUE_BOLD_BRIGHT = "\033[1;94m"; // BLUE
		public static final String PURPLE_BOLD_BRIGHT = "\033[1;95m";// PURPLE
		public static final String CYAN_BOLD_BRIGHT = "\033[1;96m"; // CYAN
		public static final String WHITE_BOLD_BRIGHT = "\033[1;97m"; // WHITE

		// High Intensity backgrounds
		public static final String BLACK_BACKGROUND_BRIGHT = "\033[0;100m";// BLACK
		public static final String RED_BACKGROUND_BRIGHT = "\033[0;101m";// RED
		public static final String GREEN_BACKGROUND_BRIGHT = "\033[0;102m";// GREEN
		public static final String YELLOW_BACKGROUND_BRIGHT = "\033[0;103m";// YELLOW
		public static final String BLUE_BACKGROUND_BRIGHT = "\033[0;104m";// BLUE
		public static final String PURPLE_BACKGROUND_BRIGHT = "\033[0;105m"; // PURPLE
		public static final String CYAN_BACKGROUND_BRIGHT = "\033[0;106m"; // CYAN
		public static final String WHITE_BACKGROUND_BRIGHT = "\033[0;107m"; // WHITE
	}

    /**
     * 
     */
    public static final String ENDMSG = "ENDMSG ";
    /**
     * 
     */
    public static final String CR = TLAConstants.CR;
    /**
     * 
     */
    public static final String SPACE = TLAConstants.SPACE;
    /**
     * 
     */
    public static final String COLON = TLAConstants.COLON;
    public static final String DELIM = "@!@!@"; //$NON-NLS-1$
    public static final String STARTMSG = "STARTMSG "; //$NON-NLS-1$

    private static final String[] EMPTY_PARAMS = new String[0];

    /**
     * Severity - standard output
     */
    public static final int NONE = 0;
    /**
     * Severity - error
     */
    public static final int ERROR = 1;
    /**
     * Severity - bug
     */
    public static final int TLCBUG = 2;
    /**
     * Severity - warning
     */
    public static final int WARNING = 3;
    /**
     * Severity - state print
     */
    public static final int STATE = 4;

    /**
     * This value is used for printing progress in simulation and depth first search
     * mode in the same format as in model checking mode to allow
     * for easier parsing. This value appears in the output string
     * whereever there is not an applicable value for simulation mode.
     */
    public static final String NOT_APPLICABLE_VAL = "-1";

    private static MP instance = null;
	private static MPRecorder recorder = new MPRecorder();
    private final Set warningHistory;
    private static final String CONFIG_FILE_ERROR = "TLC found an error in the configuration file at line %1%\n";
    private static final SimpleDateFormat SDF = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss"); //$NON-NLS-1$ 
	private static final DecimalFormat df = new DecimalFormat("###,###.###");
	
	/**
	 * By default, do not run in debug mode which means full stack traces do not
	 * get printed to the console. Printing stack traces is known to screw up
	 * the Toolbox parser though. Hence, debug has to be turned on explicitly by
	 * passing the System property.
	 */
	private static final boolean DO_DEBUG = Boolean.getBoolean(MP.class.getName() + ".noDebug");

    /**
     * The internal instance
     */
    static
    {
        instance = new MP();
    }

    /**
     * Private constructor to avoid instantiations
     */
    private MP()
    {
        warningHistory = new Set();
    }

    /**
     * Returns the formatted message
     * @param messageClass one of ERROR, TLCBUG
     * @param messageCode see ErrorCodes class
     * @param parameters string of parameters to be replaced in the message
     * @return the formatted message
     */
    public synchronized static String getMessage(int messageClass, int messageCode, String[] parameters)
    {

        if (parameters == null)
        {
            parameters = EMPTY_PARAMS;
        }
        DebugPrinter.print("entering MP.getMessage() with error code " + messageCode + " and " + parameters.length //$NON-NLS-1$
                + " parameters"); //$NON-NLS-1$

        for (int i = 0; i < parameters.length; i++)
        {
            DebugPrinter.print("param " + i + ": '" + parameters[i] + "'"); //$NON-NLS-1$
        }

        StringBuffer b = new StringBuffer();

        if (TLCGlobals.tool)
        {
            // for the tool we always print the message class
            // and message code
            b.append(DELIM).append(STARTMSG).append(messageCode).append(COLON).append(messageClass).append(SPACE)
                    .append(DELIM).append(CR);
        } else
        {
            // depending on message class add different prefix
            switch (messageClass) {
            case ERROR:
                b.append("Error: ");
                break;
            case TLCBUG:
                b.append("TLC Bug: ");
                break;
            case STATE:
                b.append("State ");
                break;
            case WARNING:
                b.append("Warning: ");
                break;
            case NONE:
            default:
                break;
            }
        }
        
        b.append(getMessage0(messageClass, messageCode, parameters));

        if (TLCGlobals.tool)
        {
            // for the tool we always print the message code
            b.append(CR).append(DELIM).append(ENDMSG).append(messageCode).append(SPACE).append(DELIM);
        } else
        {

            // post processing
            switch (messageClass) {
            case WARNING:
            	if (instance.warningHistory.isEmpty()) {
            		b.append("\n(Use the -nowarning option to disable this warning.)");
            	}
                break;
            case ERROR:
                if (TLCGlobals.tool)
                {
                    b.append("\n--End Error.");
                }
                break;
            case TLCBUG:
            case NONE:
            default:
                break;
            }
        }
        DebugPrinter.print("Leaving getMessage()"); //$NON-NLS-1$
        return b.toString();
    }

	private static String getMessage0(int messageClass, int messageCode, String[] parameters) {
        final StringBuffer b = new StringBuffer();
		// fill with different message depending on the error code
        switch (messageCode) {
        case EC.UNIT_TEST:
            b.append("[%1%][%2%]");
            break;
        case EC.SYSTEM_STACK_OVERFLOW:
            b.append("This was a Java StackOverflowError. It was probably the result\n"
                    + "of an incorrect recursive function definition that caused TLC to enter\n"
                    + "an infinite loop when trying to compute the function or its application\n"
                    + "to an element in its putative domain.");
            break;
        case EC.SYSTEM_OUT_OF_MEMORY:
            b.append("Java ran out of memory.  Running Java with a larger memory allocation\n"
                    + "pool (heap) may fix this.  But it won't help if some state has an enormous\n"
                    + "number of successor states, or if TLC must compute the value of a huge set.");
            break;
        case EC.SYSTEM_OUT_OF_MEMORY_LIVENESS:
            b.append("Java ran out of memory during liveness checking.  Running Java with a larger memory\n"
                    + "allocation pool (heap) may fix this.  But it won't help if paths in the liveness graph\n"
                    + "have an enormous number of states.");
            break;
        case EC.SYSTEM_OUT_OF_MEMORY_TOO_MANY_INIT:
            b.append("Out Of Memory. There are probably too many initial states.");
            break;
        case EC.SYSTEM_ERROR_READING_POOL:
            b.append("when reading the disk (StatePoolReader.run):\n%1%");
            break;

        case EC.SYSTEM_CHECKPOINT_RECOVERY_CORRUPT:
            b.append("TLC encountered the following error while restarting from a "
                    + "checkpoint;\n the checkpoint file is probably corrupted.\n%1%");
            break;
        case EC.SYSTEM_ERROR_READING_STATES:
            b.append("TLC encountered the following error reading the %1% of unexplored states:\n%2%");
            break;
        case EC.SYSTEM_ERROR_WRITING_STATES:
            b.append("TLC encountered the following error writing the %1% of unexplored states:\n%2%");
            break;

        case EC.SYSTEM_ERROR_WRITING_POOL:
            b.append("when writing the disk (StatePoolWriter.run):\n%1%");
            break;
		case EC.SYSTEM_ERROR_CLEANING_POOL:
			if (messageClass == ERROR) {
				b.append("Exception cleaning up an obsolete disk file.\n%1%");
			} else if (messageClass == WARNING) {
				b.append("Failed to clean up an obsolete disk file. Please manually delete %1% if free disk space is low.");
			}
            break;

        case EC.SYSTEM_DISKGRAPH_ACCESS:
            b.append("DiskGraph.toString()");
            break;
        case EC.SYSTEM_FILE_NULL:
            b.append("File must be not null");
            break;

        case EC.SYSTEM_INTERRUPTED:
            b.append("Thread has been interrupted.");
            break;

        case EC.SYSTEM_INDEX_ERROR:
            b.append("Index error.");
            break;

        case EC.SYSTEM_STREAM_EMPTY:
            b.append("The provided input stream was null, empty or could not be accessed.");
            break;
        case EC.SYSTEM_UNABLE_TO_OPEN_FILE:
            b.append("Unable to open %1%.\n%2%");
            break;
        case EC.SYSTEM_UNABLE_NOT_RENAME_FILE:
            b.append("Unable not rename file during the clean-up.");
            break;

        case EC.SYSTEM_DISK_IO_ERROR_FOR_FILE:
            b.append("Disk I/O error accessing the file for %1%.");
            break;

        case EC.SYSTEM_METADIR_EXISTS:
            b.append("TLC writes its files to a directory whose name is generated from the current "
                    + "time.\nThis directory should be %1%, but that directory already exists.\n"
                    + "Trying to run TLC again will probably fix this problem.");
            break;

        case EC.SYSTEM_METADIR_CREATION_ERROR:
            b.append("TLC could not make a directory %1% for the disk files it needs to write.");
            break;
        /* ----------------------------------------------------------------- */
        case EC.WRONG_COMMANDLINE_PARAMS_TLC:
            b.append("%1%\nUsage: java tlc2.TLC [-option] inputfile");
            break;
        case EC.WRONG_COMMANDLINE_PARAMS_SIMULATOR:
            b.append("%1%\nUsage: java tlc2.Simulator [-option] inputfile");
            break;
        /* ----------------------------------------------------------------- */
        case EC.TLC_VERSION:
            b.append("TLC2 %1%");
            break;

        case EC.TLC_PP_FORMATING_VALUE:
            b.append("error while formating %1%\n%2%");
            break;

        case EC.TLC_PP_PARSING_VALUE:
            b.append("error while parsing %1%\n%2%");
            break;

        case EC.TLC_METADIR_EXISTS:
            b.append("TLC writes its files to a directory which name is generated"
                    + " from the current time.\nThis directory should be %1%"
                    + ", but that directory already exists.\n"
                    + "Trying to run TLC again will probably fix this problem.\n");
            break;
        case EC.TLC_METADIR_CAN_NOT_BE_CREATED:
            b.append("TLC could not make a directory for the disk files" + " it needs to write.\n");
            break;

        case EC.TLC_INITIAL_STATE:
            b.append("%1%\nWhile working on the initial state:\n%2%");
            break;

        case EC.TLC_NESTED_EXPRESSION:
            b.append("The error occurred when TLC was evaluating the nested"
                    + "\nexpressions at the following positions:\n%1%");
            break;

        case EC.TLC_ASSUMPTION_FALSE:
            b.append("Assumption %1% is false.");
            break;
        case EC.TLC_SANY_START:
            b.append("Starting SANY...");
            break;
        case EC.TLC_SANY_END:
            b.append("SANY finished.");
            break;
        case EC.TLC_ASSUMPTION_EVALUATION_ERROR:
            b.append("Evaluating assumption %1% failed.\n%2%");
            break;
        case EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_INITIAL:
            b.append("State is not completely specified by the initial predicate:\n%1%");
            break;
        case EC.TLC_INVARIANT_VIOLATED_INITIAL:
            b.append("Invariant %1% is violated by the initial state:\n%2%");
            break;
        case EC.TLC_PROPERTY_VIOLATED_INITIAL:
            b.append("Property %1% is violated by the initial state:\n%2%");
            break;

        case EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT:
			if (parameters.length == 3) {
				b.append(
						"Successor state is not completely specified by action %1% of the next-state relation. The following variable%2% not assigned: %3%.\n");
			} else if (parameters.length == 2) {
				b.append(
						"Successor state is not completely specified by the next-state action. The following variable%1% not assigned: %2%.\n");
			} else {
				b.append("Successor state is not completely specified by the next-state action.\n");
			}
            break;
        case EC.TLC_INVARIANT_VIOLATED_BEHAVIOR:
            b.append("Invariant %1% is violated.");
            break;
        case EC.TLC_INVARIANT_VIOLATED_LEVEL:
        	b.append("The invariant %1% is not a state predicate (one with no primes or temporal operators).");
        	if (parameters.length > 1) {
        		b.append("\nNote that a bug can cause TLC to incorrectly report this error.\n"
        				+ "If you believe your TLA+ or PlusCal specification to be correct,\n"
        				+ "please check if this bug described in LevelNode.java starting at line 590ff affects you.");
        	}
            break;

        case EC.TLC_INVARIANT_EVALUATION_FAILED:
            if (parameters.length == 1) {
                b.append("Evaluating invariant %1% failed.");
            }
            else if (parameters.length == 2) {
                b.append("Evaluating invariant %1% failed.\n%2%");
            }
            break;

        case EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR:
            b.append("Action property %1%" + " is violated.");
            break;

        case EC.TLC_ACTION_PROPERTY_EVALUATION_FAILED:
            if (parameters.length == 1) {
                b.append("Evaluating action property %1% failed.");
            }
            else if (parameters.length == 2) {
                b.append("Evaluating action property %1% failed.\n%2%");
            }
            break;

        case EC.TLC_DEADLOCK_REACHED:
            b.append("Deadlock reached.");
            break;
        case EC.TLC_COUNTER_EXAMPLE:
            b.append("The following behavior constitutes a counter-example:\n");
            break;
        case EC.TLC_TEMPORAL_PROPERTY_VIOLATED:
            b.append("Temporal properties were violated.\n");
            break;

        // this is a TLC bug
        case EC.TLC_STATES_AND_NO_NEXT_ACTION:
            b.append("No next state actions defined to generate successor states from.");
            break;
        case EC.TLC_FAILED_TO_RECOVER_NEXT:
            b.append("Failed to recover the next state from its fingerprint.");
            break;
        // this is a TLC bug
        case EC.TLC_FAILED_TO_RECOVER_INIT:
            b.append("Failed to recover the initial state from its fingerprint.");
            break;

        case EC.TLC_BUG:
            b.append("This is probably a TLC bug(%1%).");
            break;

        case EC.TLC_FINGERPRINT_EXCEPTION:
            b.append("TLC was unable to fingerprint."
                + "\n"
                + "\nFingerprint Stack Trace:"
                + "\n%1%"
                + "\nReason:"
                + "\n%2%"); // reason must come last, with nothing following, because Tool cannot parse the embedded error otherwise

            break;

        case EC.TLC_NO_STATES_SATISFYING_INIT:
            b.append("There is no state satisfying the initial state predicate.");
            break;

        case EC.TLC_STRING_MODULE_NOT_FOUND:
            b.append("This is a TLC bug: TLC could not find its built-in String module.\n");
            break;

        case EC.TLC_BACK_TO_STATE:
            if (TLCGlobals.tool) {
                // format same as state printing for easier
                // parsing by toolbox
                if (parameters.length == 1) {
                    b.append("%1%: ").append(TLAConstants.BACK_TO_STATE).append("\n");
                }
                else if (parameters.length == 2) {
                    b.append("%1%: ").append(TLAConstants.BACK_TO_STATE).append(": %2%\n");
                }
            } else {
                if (parameters.length == 1) {
                    b.append(TLAConstants.BACK_TO_STATE).append(" %1%\n");
                }
                else if (parameters.length == 2) {
                    b.append(TLAConstants.BACK_TO_STATE).append(" %1%: %2%\n");
                }
            }
            break;

        case EC.TLC_ERROR_STATE:
            b.append("The error state is:\n");
            break;

        case EC.TLC_BEHAVIOR_UP_TO_THIS_POINT:
            b.append("The behavior up to this point is:");
            break;

        case EC.TLC_REPORTER_DIED:
            b.append("Progress report thread died.");
            break;

        case EC.TLC_AAAAAAA:
            b.append("AAAAAA");
            break;
        case EC.TLC_REGISTRY_INIT_ERROR:
            b.append("TLA+ Registry initialization error. The name %1% is already in use.");
            break;

        /* ************************************************************************ */
        case EC.CHECK_FAILED_TO_CHECK:
            b.append("TLC failed in checking traces.");
            break;

        case EC.CHECK_PARAM_USAGE:
            b.append("Usage: java tlc2.tool.CheckImplFile [-option] inputfile");
            break;

        case EC.CHECK_PARAM_MISSING_TLA_MODULE:
            b.append("Missing input TLA+ module.");
            break;

        case EC.CHECK_PARAM_EXPECT_CONFIG_FILENAME:
            b.append("Expect a file name for -config option.");
            break;

        case EC.CHECK_PARAM_NEED_TO_SPECIFY_CONFIG_DIR:
            b.append("need to specify the metadata directory for recovery.");
            break;

        case EC.CHECK_PARAM_WORKER_NUMBER_REQUIRED:
            b.append("Worker number required. But encountered %1%");
            break;

        case EC.CHECK_PARAM_WORKER_NUMBER_TOO_SMALL:
            b.append("At least one worker is required.");
            break;

        case EC.CHECK_PARAM_WORKER_NUMBER_REQUIRED2:
            b.append("Expect an integer for -workers option.");
            break;

        case EC.CHECK_PARAM_DEPTH_REQUIRED:
            b.append("Depth must be an integer. But encountered %1%");
            break;

        case EC.CHECK_PARAM_DEPTH_REQUIRED2:
            b.append("Expect an integer for -depth option.");
            break;

        case EC.CHECK_PARAM_TRACE_REQUIRED:
            b.append("Expect a filename for -trace option.");
            break;

        case EC.CHECK_PARAM_COVREAGE_REQUIRED:
            b.append("An integer for coverage report interval required. But encountered %1%");
            break;

        case EC.CHECK_PARAM_COVREAGE_REQUIRED2:
            b.append("Coverage report interval required.");
            break;

        case EC.CHECK_PARAM_COVREAGE_TOO_SMALL:
            b.append("Expect a nonnegative integer for -coverage option.");
            break;

        case EC.CHECK_PARAM_UNRECOGNIZED:
            if (parameters.length == 1) {
                b.append("Unrecognized option: %1%");
            }
            else if (parameters.length == 2) {
                b.append("Unrecognized option in file %2%: %1%");
            }
            break;
        case EC.CHECK_PARAM_TOO_MANY_INPUT_FILES:
            b.append("More than one input files: %1% and %2%");
            break;

        case EC.CHECK_COULD_NOT_READ_TRACE:
            b.append("TLC could not read in the trace. %1%");
            break;

        case EC.TLC_PARSING_FAILED:
            b.append("Parsing or semantic analysis failed.");
            break;
        case EC.TLC_PARSING_FAILED2:
            b.append("Parsing or semantic analysis failed.%1%");
            break;

        /* ************************************************************************ */
        case EC.TLC_VALUE_ASSERT_FAILED:
            b.append("The first argument of Assert evaluated to FALSE; the second argument was:\n%1%");
            break;

        case EC.TLC_FP_NOT_IN_SET:
            b.append("The fingerprint is not in set.");
            break;
        case EC.TLC_FP_COMPLETED:
            b.append("%1%, work completed. Thank you!");
            break;

        case EC.TLC_PARAMETER_MUST_BE_POSTFIX:
            b.append("Parameter must be a postfix operator");
            break;

        case EC.TLC_COULD_NOT_DETERMINE_SUBSCRIPT:
            b.append("TLC could not determine if the subscript of the next-state relation contains"
                    + "\nall state variables. Proceed with fingers crossed.");
            break;

        case EC.TLC_SUBSCRIPT_CONTAIN_NO_STATE_VAR:
            b.append("The subscript of the next-state relation specified by the specification"
                    + "\ndoes not seem to contain the state variable %1%");
            break;

        case EC.TLC_WRONG_TUPLE_FIELD_NAME:
            b.append("Tuple field name %1% is not an integer.");
            break;

        case EC.TLC_WRONG_RECORD_FIELD_NAME:
            b.append("Record field name %1% is not a string.");
            break;

        case EC.TLC_UNCHANGED_VARIABLE_CHANGED:
            b.append("The variable %1% was changed while it is specified as UNCHANGED at\n%2%");
            break;

        case EC.TLC_EXCEPT_APPLIED_TO_UNKNOWN_FIELD:
            b.append("The EXCEPT was applied to non-existing fields of the value at\n%1%");
            break;
            
        case EC.TLC_SYMMETRY_SET_TOO_SMALL:
        	b.append("The set%1% %2% %3% been defined to be a symmetry set but contain%4% less than two elements.");
        	break;
            
        case EC.TLC_SPECIFICATION_FEATURES_TEMPORAL_QUANTIFIER:
        	b.append("TLC does not support temporal existential, nor universal, quantification over state variables.");
        	break;
        /* ************************************************************************ */
        case EC.TLC_MODULE_TLCGET_UNDEFINED:
            b.append("TLCGet(%1%) was undefined.");
            break;

        case EC.TLC_MODULE_OVERFLOW:
            b.append("Overflow when computing %1%");
            break;

        case EC.TLC_MODULE_ONE_ARGUMENT_ERROR:
            b.append("The argument of %1% should be a %2%, but instead it is:\n%3%");
            break;

        case EC.TLC_MODULE_ARGUMENT_ERROR:
            b.append("The %1% argument of %2% should be a %3%, but instead it is:\n%4%");
            break;

        case EC.TLC_MODULE_ARGUMENT_ERROR_AN:
            b.append("The %1% argument of %2% should be an %3%, but instead it is:\n%4%");
            break;

        case EC.TLC_MODULE_ARGUMENT_NOT_IN_DOMAIN:
            b.append("The %1% argument of %2% must be in the domain of its %3% argument:\n%4%\n, but"
                    + " instead it is\n%5%");
            break;

        case EC.TLC_MODULE_DIVISION_BY_ZERO:
            b.append("The second argument of \\div is 0.");
            break;

        case EC.TLC_MODULE_NULL_POWER_NULL:
            b.append("0^0 is undefined.");
            break;

        case EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE:
            b.append("Applying %1% to the following value,\nwhich is not %2%:\n%3%");
            break;

        case EC.TLC_MODULE_COMPARE_VALUE:
            b.append("Attempted to compare %1% with the value\n%2%");
            break;

        case EC.TLC_MODULE_APPLY_EMPTY_SEQ:
            b.append("Attempted to apply %1% to the empty sequence.");
            break;

        case EC.TLC_MODULE_CHECK_MEMBER_OF:
            b.append("Attempted to check if the value:\n%1%\nis an element of %2%.");
            break;

        case EC.TLC_MODULE_BAG_UNION1:
            b.append("Attemtped to apply BagUnion to the following set, whose\nelement is not a bag:\n%1%");
            break;

        case EC.TLC_MODULE_TRANSITIVE_CLOSURE:
            b.append("Attemtped to apply TransitiveClosure to a set containing\nthe following value:\n%1%");
            break;

        case EC.TLC_MODULE_COMPUTING_CARDINALITY:
            b.append("Attemtped to compute cardinality of the value\n%1%");
            break;
        case EC.TLC_MODULE_EVALUATING:
            b.append("Evaluating an expression of the form %1% when s is not a %2%:\n%3%");
            break;

        case EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE:
            b.append("Attempted to apply the operator overridden by the Java method"
                    + "\n%1%,\nbut it produced the following error:\n%2%");
            break;
        case EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_LOADED:
            b.append("Loading %1% operator override from %2% with signature: %3%.");
            break;
        case EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_MISMATCH:
            b.append("Failed to match %1% operator override from %2% with signature: %3%.");
            break;
        case EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_IDENTIFIER_MISMATCH:
            b.append("Failed to match %1% operator override from %2% with signature: %3% (no such operator).");
            break;
        case EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_MODULE_MISMATCH:
            b.append("Failed to match %1% operator override from %2% with signature: %3% (no such module).");
            break;
        case EC.TLC_MODULE_OVERRIDE_STDOUT:
            b.append("%1%");
            break;
       case EC.TLC_FEATURE_UNSUPPORTED:
            b.append("%1%");
            break;
        case EC.TLC_FEATURE_UNSUPPORTED_LIVENESS_SYMMETRY:
            b.append("Declaring symmetry during liveness checking is dangerous. "
            		+ "It might cause TLC to miss violations of the stated liveness properties. "
            		+ "Please check liveness without symmetry defined.");
            break;
        case EC.TLC_FEATURE_LIVENESS_CONSTRAINTS:
        	// Specifying Systems Section 14.3.5 page 247.
        	// https://lamport.azurewebsites.net/tla/book.html
			b.append("Declaring state or action constraints during liveness checking is dangerous: "
					+ "Please read section 14.3.5 on page 247 of Specifying Systems "
					+ "(https://lamport.azurewebsites.net/tla/book.html) and optionally the "
					+ "discussion at https://discuss.tlapl.us/msg00994.html for more details.");
            break;

        /* Liveness errors */
        case EC.TLC_LIVE_BEGRAPH_FAILED_TO_CONSTRUCT:
            b.append("BEGraph.GetPath: Failed to construct a path.");
            break;
        case EC.TLC_LIVE_IMPLIED:
            b.append("Implied-temporal checking--satisfiability problem has %1% branches.");
            break;
        case EC.TLC_LIVE_CANNOT_HANDLE_FORMULA:
        	if (parameters.length > 1) {
        		b.append("TLC cannot handle the temporal formula %1%:\n%2%");
        	} else {
        		b.append("TLC cannot handle the temporal formula %1%");
        	}
            break;
        case EC.TLC_LIVE_WRONG_FORMULA_FORMAT:
            b.append("Temporal formulas containing actions must be of forms <>[]A or []<>A.");
            break;
        case EC.TLC_LIVE_ENCOUNTERED_ACTIONS:
            b.append("TLC encountered actions when computing closure.");
            break;
        case EC.TLC_LIVE_STATE_PREDICATE_NON_BOOL:
            b.append("A state predicate was evaluated to a non-boolean value.");
            break;
        case EC.TLC_LIVE_CANNOT_EVAL_FORMULA:
            b.append("Can not evaluate a temporal formula %1%F.");
            break;
        case EC.TLC_LIVE_ENCOUNTERED_NONBOOL_PREDICATE:
            b.append("Encountered an action predicate that's not a boolean.");
            break;
        case EC.TLC_LIVE_FORMULA_TAUTOLOGY:
            b.append("Temporal formula is a tautology (its negation is unsatisfiable).");
            break;

        case EC.TLC_EXPECTED_VALUE:
            b.append("TLC expected a %1% value, but did not find one. %2%");
            break;
        case EC.TLC_EXPECTED_EXPRESSION:
            b.append("TLC expected a %1% expression, but did not find one.\n%2%");
            break;
        case EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING:
            b.append("In computing %1%, TLC expected a %2% expression," + "\nbut instead found %3%.\n%4%");
            break;
        case EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING2:
            b.append("In computing %1%, TLC expected a %2% expression," + "\nbut didn't find one.\n%3%");
            break;

        case EC.TLC_CHOOSE_ARGUMENTS_WRONG:
            b.append("The arguments to %1% are not appropriate.");
            break;

        case EC.TLC_CHOOSE_UPPER_BOUND:
            b.append("Choose can only deal with numbers up to %1%");
            break;

        case EC.TLC_FP_VALUE_ALREADY_ON_DISK:
            b.append("DiskFPSet.mergeNewEntries: %1% is already on disk.\n");
            break;

        case EC.SANY_PARSER_CHECK_1:
            b.append("TLA+ Parser sanity check.");
            break;

        case EC.SANY_PARSER_CHECK_2:
            b.append("TLA+ Parser check: Assertion error in epa().");
            break;

        case EC.SANY_PARSER_CHECK_3:
            b.append("TLA+ Parser check: Assertion error in SBracketCases().");
            break;

        case EC.TLC_ARGUMENT_MISMATCH:
            b.append("Argument mismatch in operator application.%1");
            break;

        case EC.TLC_TOO_MNY_POSSIBLE_STATES:
            b.append("Too many possible next states for the last state in the trace.");
            break;
        case EC.TLC_ERROR_REPLACING_MODULES:
            b.append("Found a Java class for module %1%, but unable to read\n" + "it as a Java class object. %2%");
            break;

        /*------------------------------------------- */
        // TLC distributed 
        case EC.TLC_DISTRIBUTED_SERVER_RUNNING:
            b.append("TLC server at %1% is ready (").append(now()).append(")");
            break;
        case EC.TLC_DISTRIBUTED_WORKER_REGISTERED:
            b.append("Registration for worker at %1% completed (").append(now()).append(")");
            break;
        case EC.TLC_DISTRIBUTED_WORKER_DEREGISTERED:
            b.append("TLC worker %1% disconnected (").append(now()).append(")");
            break;
        case EC.TLC_DISTRIBUTED_WORKER_STATS:
        	//new Date() + " Worker: " + name + " Sent: " + sentStates + " Rcvd: " + receivedStates
			b.append("Worker: %1% Sent: %2% Rcvd: %3% CacheRatio: %4% (").append(now()).append(")");
            break;
        case EC.TLC_DISTRIBUTED_SERVER_NOT_RUNNING:
            b.append("TLCServer is gone due to %1%, exiting worker... (").append(now()).append(")");
            break;
        case EC.TLC_DISTRIBUTED_SERVER_FINISHED:
            b.append("TLCServer has finished, exiting worker... (").append(now()).append(")");
            break;
		case EC.TLC_DISTRIBUTED_VM_VERSION:
			b.append(
					"VM does not allow to get the UnicastRef port.\nWorker will be identified with port 0 in output (")
					.append(now()).append(")");
			break;
		case EC.TLC_DISTRIBUTED_WORKER_LOST:
			b.append("TLC worker connection lost %1% (").append(now()).append(")");
			break;
		case EC.TLC_DISTRIBUTED_EXCEED_BLOCKSIZE:
			b.append("Trying to limit max block size (to recover from transport failure): %1% (").append(now()).append(")");
			break;
		case EC.TLC_DISTRIBUTED_SERVER_FPSET_REGISTERED:
			b.append("%1% out of %2% FPSet server(s) registered (").append(now()).append(")");
			break;
		case EC.TLC_DISTRIBUTED_SERVER_FPSET_WAITING:
			b.append("Waiting for %1% FPSet server(s) to register (").append(now()).append(")");
			break;
            
        /*------------------------------------------- */
        case EC.TLC_STARTING:
            b.append("Starting... (").append(now()).append(")");
            break;
        case EC.TLC_FINISHED:
            b.append("Finished in %1% at (").append(now()).append(")");
            break;
		/*
		 * The two startup banners below are parsed by the Toolbox in
		 * org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider.
		 * startupMessagePattern.  Remember to update when the banners below 
		 * get changed 
		 * (see org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProviderTest)!!!
		 */
        case EC.TLC_MODE_MC:
            b.append("Running breadth-first search Model-Checking with fp %13% and seed %12% with %1% worker%2% on %3% cores with %10%MB heap and %11%MB offheap memory");
            if (!"".equals(parameters[13])) {
            	b.append(" [pid: %14%]");
            } else {
				// Make sure subsequent parameters, %15%... are processed below in the
				// replaceString method. replaceString terminates if a string is not present,
				// thus we replace %14% with the zero-length string to not change the output but
				// to make replaceString happy.
            	b.append("%14%");
            }
            b.append(" (%4% %5% %6%, %7% %8% %9%, %15%, %16%).");
            break;
        case EC.TLC_MODE_MC_DFS:
            b.append("Running depth-first search Model-Checking with fp %13% and seed %12% with %1% worker%2% on %3% cores with %10%MB heap and %11%MB offheap memory");
            if (!"".equals(parameters[13])) {
            	b.append(" [pid: %14%]");
            } else {
            	// see TLC_MODE_MC above.
            	b.append("%14%");
            }
     		b.append(" (%4% %5% %6%, %7% %8% %9%).");
            break;
        case EC.TLC_MODE_SIMU:
            b.append("Running Random Simulation with seed %1% with %2% worker%3% on %4% cores with %11%MB heap and %12%MB offheap memory");
            if (!"".equals(parameters[12])) {
            	b.append(" [pid: %13%]");
            } else {
            	// see TLC_MODE_MC above.
            	b.append("%13%");
            }
            b.append(" (%5% %6% %7%, %8% %9% %10%).");
            break;
        case EC.TLC_COMPUTING_INIT:
            b.append("Computing initial states...");
            break;
        case EC.TLC_COMPUTING_INIT_PROGRESS:
            b.append("Computed %1% initial states...");
            break;
        case EC.TLC_INIT_GENERATED1:
			b.append("Finished computing initial states: %1% distinct state%2% generated at ")
					.append(now()).append(".");
            break;
        case EC.TLC_INIT_GENERATED2:
			b.append("Finished computing initial states: %1% state%2% generated, with %3% of them distinct at ")
					.append(now()).append(".");
            break;
        case EC.TLC_INIT_GENERATED3:
			b.append("Finished computing initial states: %1% states generated.\n"
					+ "Because TLC recovers from a previous checkpoint, only %2% of them require further exploration at ")
					.append(now()).append(".");
            break;
        case EC.TLC_INIT_GENERATED4:
            b.append("Finished computing initial states: %1% states generated, with %2% of them distinct.");
            break;
        case EC.TLC_CHECKING_TEMPORAL_PROPS:
			b.append("Checking %3%temporal properties for the %1% state space with %2% total distinct states at (")
					.append(now()).append(")");
            break;
		case EC.TLC_CHECKING_TEMPORAL_PROPS_END:
			b.append("Finished checking temporal properties in %1% at " + now());
	        break;
        case EC.TLC_SUCCESS:
            b.append("Model checking completed. No error has been found.\n"
                    + "  Estimates of the probability that TLC did not check all reachable states\n");
            if (parameters.length == 1) {
            	b.append("  because two distinct states had the same fingerprint:\n" + "  calculated (optimistic):  %1%");
            } else {
            	b.append("  because two distinct states had the same fingerprint:\n"
            			+ "  calculated (optimistic):  %1%\n" + "  based on the actual fingerprints:  %2%");
            }
            break;
        case EC.TLC_SEARCH_DEPTH:
			b.append("The depth of the complete state graph search is %1%.");
            break;
        case EC.TLC_STATE_GRAPH_OUTDEGREE:
			b.append("The average outdegree of the complete state graph is %2% (minimum is %1%, the maximum %4% and the 95th percentile is %3%).");
            break;
       case EC.TLC_CHECKPOINT_START:
            b.append("Checkpointing of run %1%");
            break;
        case EC.TLC_CHECKPOINT_END:
            b.append("Checkpointing completed at (").append(now()).append(")");
            break;
        case EC.TLC_CHECKPOINT_RECOVER_START:
            b.append("Starting recovery from checkpoint %1%");
            break;
        case EC.TLC_CHECKPOINT_RECOVER_END:
            b.append("Recovery completed. %1% states examined. %2% states on queue.");
            break;
        case EC.TLC_CHECKPOINT_RECOVER_END_DFID:
            b.append("Recovery completed. %1% states examined.");
            break;

        case EC.TLC_STATS:
            b.append("%1% states generated, %2% distinct states found, %3% states left on queue.");
            break;
        case EC.TLC_STATS_DFID:
            b.append("%1% states generated, %2% distinct states found.");
            break;
        case EC.TLC_STATS_SIMU:
            b.append("The number of states generated: %1%\nSimulation using seed %2% and aril %3%");
            break;
        case EC.TLC_PROGRESS_STATS:
        	if (parameters.length == 4) {
				b.append("Progress(%1%) at " + now() + ": %2% states generated, "
						+ "%3% distinct states found, " + "%4% states left on queue.");
        	} else if (parameters.length == 6) {
        		b.append("Progress(%1%) at " + now() + ": %2% states generated ("
        				+ "%5% s/min), %3% distinct states found (%6% ds/min), %4% states left on queue.");
        	}
            break;
        case EC.TLC_PROGRESS_START_STATS_DFID:
            b.append("Starting level %1%: %2% states generated, %3% distinct states found.");
            break;
        case EC.TLC_PROGRESS_STATS_DFID:
            if (TLCGlobals.tool)
            {
                // same format as model checking progress reporting for easier parsing by the toolbox
                b.append("Progress(" + NOT_APPLICABLE_VAL + ") at " + now()
                        + ": %1% states generated, %2% distinct states found, " + NOT_APPLICABLE_VAL
                        + " states left on queue.");
            } else
            {
                b.append("Progress: %1% states generated, %2% distinct states found.");
            }
            break;
        case EC.TLC_PROGRESS_SIMU:
            if (TLCGlobals.tool)
            {
                // same format as model checking progress reporting for easier parsing by the toolbox
                b.append("Progress(" + NOT_APPLICABLE_VAL + ") at " + now()
                        + ": %1% states generated, " + NOT_APPLICABLE_VAL + " distinct states found, "
                        + NOT_APPLICABLE_VAL + " states left on queue.");
            } else
            {
                b.append("Progress: %1% states checked.");
            }
            break;

        case EC.TLC_COVERAGE_START:
            b.append("The coverage statistics at " + now());
            break;
        case EC.TLC_COVERAGE_VALUE:
            b.append("  %1%: %2%");
            break;
        case EC.TLC_COVERAGE_VALUE_COST:
            b.append("  %1%: %2%:%3%");
            break;
        case EC.TLC_COVERAGE_INIT:
       		b.append("%1%: %2%:%3%");
            break;
        case EC.TLC_COVERAGE_NEXT:
       		b.append("%1%: %2%:%3%");
            break;
        case EC.TLC_COVERAGE_PROPERTY:
       		b.append("%1%");
            break;
        case EC.TLC_COVERAGE_MISMATCH:
			b.append(
					"CostModel lookup failed for expression <%1%>. Reporting costs into <%2%> instead (Safety and Liveness checking is unaffected. Please report a bug.)");
        	break;
        case EC.TLC_COVERAGE_END:
            b.append("End of statistics.");
            break;
		case EC.TLC_COVERAGE_END_OVERHEAD:
			b.append("End of statistics (please note that for performance reasons large models\n"
					+ "are best checked with coverage and cost statistics disabled).");
            break;

        /* ************************************************************************ */
        // errors evaluating the config file and the MC file
        case EC.TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM:
            b.append("The constant parameter %1% is not assigned a value by the configuration file.");
            break;
        case EC.TLC_CONFIG_RHS_ID_APPEARED_AFTER_LHS_ID:
            b.append("In the configuration file, the identifier %1% appears\n"
                    + "on the right-hand side of a <- after already appearing on the\n" + "left-hand side of one.");
            break;
        case EC.TLC_CONFIG_WRONG_SUBSTITUTION:
            b.append("The configuration file substitutes for %1% with the undefined identifier %2%.");
            break;
        case EC.TLC_CONFIG_UNDEFINED_OR_NO_OPERATOR:
            b.append("In evaluation, the identifier %1% is either undefined or not an operator.\n%2%");
            break;
        case EC.TLC_CONFIG_SUBSTITUTION_NON_CONSTANT:
            b.append("The configuration file substitutes constant %1% with non-constant %2%%3%");
            break;
        case EC.TLC_CONFIG_WRONG_SUBSTITUTION_NUMBER_OF_ARGS:
            b.append("The configuration file substitutes for %1% with %2% of different number of arguments.");
            break;
        case EC.TLC_CONFIG_ID_DOES_NOT_APPEAR_IN_SPEC:
            b.append("In the configuration file, the identifier %1% does not appear in the specification.");
            break;
        case EC.TLC_CONFIG_NOT_BOTH_SPEC_AND_INIT:
            b.append("The configuration file cannot specify both INIT/NEXT and SPECIFICATION fields.");
            break;
        case EC.TLC_CONFIG_ID_REQUIRES_NO_ARG:
            if (parameters.length == 1) {
                b.append("TLC requires %1% not to take any argument.");
            }
            else if (parameters.length == 2) {
                b.append("TLC requires %1% not to take any argument, but one was given: %2%");
            }
            break;
        case EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED:
            b.append("The %1% %2% specified in the configuration file" + "\nis not defined in the specification.");
            break;
        case EC.TLC_CONFIG_ID_HAS_VALUE:
            b.append("The %1% of %2% is equal to %3%");
            break;
        case EC.TLC_CONFIG_MISSING_INIT:
            b.append("The configuration file did not specify the initial state predicate." +
                     // The below part of the error message was added by LL on 15 Nov 2012
            		 //
            		 //	ldq, 13 Feb 2020: I don't think this is semantically correct; I receive
                     //			no errors when defining a specification that references
            		 //			a formula which is a parameterized INSTANCE. I *do* receive
                     //			such an error when that formula is being constrained via
            		 //			the temporal existential qualifier.
                     "\nCan also be caused by trying to run TLC on a specification from" +
                     "\na module imported with a parameterized INSTANCE statement.");
            break;
        case EC.TLC_CONFIG_MISSING_NEXT:
            b.append("The configuration file did not specify the next state predicate.");
            break;
        case EC.TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT:
            b.append("The %1% %2% cannot be a constant.");
            break;
        case EC.TLC_CONFIG_OP_NO_ARGS:
            b.append("The operator %1% cannot take any argument.");
            break;
        case EC.TLC_CONFIG_OP_NOT_IN_SPEC:
            b.append("The operator %1% is not defined in the spec.");
            break;
        case EC.TLC_CONFIG_OP_IS_EQUAL:
            b.append("The operator %1%, which equals %2%,\ncannot be used as a %3%");
            break;
        case EC.TLC_CONFIG_SPEC_IS_TRIVIAL:
            b.append("The spec is trivially false because %1% is false.");
            break;
        case EC.TLC_CANT_HANDLE_SUBSCRIPT:
            b.append("TLC cannot handle subscript %1%");
            break;
        case EC.TLC_CANT_HANDLE_CONJUNCT:
            b.append("TLC cannot handle this conjunct of the spec:\n%1%");
            break;
        case EC.TLC_CANT_HANDLE_TOO_MANY_NEXT_STATE_RELS:
            b.append("The specification contains more than one conjunct of the form [][Next]_v,"
                    + "\nbut TLC can handle only specifications with one next-state relation.");
            break;
        case EC.TLC_TRACE_TOO_LONG:
            b.append("The specification contains one or more behaviors with 65536 or more states,"
                    + "\nbut TLC can only handle behaviors of length up to 65535 states. The last\n"
                    + "state in the behavior is:\n%1%");
        	break;
        case EC.TLC_CONFIG_PROPERTY_NOT_CORRECTLY_DEFINED:
            b.append("The property %1% is not correctly defined.");
            break;
        case EC.TLC_CONFIG_OP_ARITY_INCONSISTENT:
            b.append("The arity of the operator %1% is inconsistent in the configuration file.");
            break;
        case EC.TLC_CONFIG_NO_STATE_TYPE:
            b.append("The configuration file did not specify types for state variables.");
            break;
        case EC.TLC_CANT_HANDLE_REAL_NUMBERS:
            b.append("TLC can't handle real numbers.\n%1%");
            break;
        case EC.TLC_INTEGER_TOO_BIG:
            b.append("TLC can't handle a number this big.\n%1%");
            break;
        case EC.TLC_NO_MODULES:
            b.append("In the configuration file, the module name %1% is not a module in the specification.");
            break;

        case EC.TLC_ENABLED_WRONG_FORMULA:
            b.append("In computing ENABLED, TLC encountered a temporal formula (%1%).\n%2%");
            break;
        case EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE:
            b.append("TLC encountered a temporal formula (%1%) when evaluating" + " a predicate or action.\n%2%");
            break;
        case EC.TLC_ENVIRONMENT_JVM_GC:
			b.append(
					"Please run the Java VM which executes TLC with a throughput optimized garbage collector by passing the \"-XX:+UseParallelGC\" property.");
            break;

        /* ************************************************************************ */
        // state printing
        case EC.TLC_STATE_PRINT1:
            b.append("%1%:\n%2%");
            break;
        case EC.TLC_STATE_PRINT2:
        	if (DO_DEBUG) {
        		b.append("%1%: %2%\n%3%fp: %4%\n");
        	} else {
        		b.append("%1%: %2%\n%3%");
        	}
            break;
        case EC.TLC_STATE_PRINT3:
            b.append("%1%:").append(TLAConstants.STUTTERING);
            break;

        /* ************************************************************************ */
        // configuration file errors
        case EC.CFG_MISSING_ID:
            b.append(CONFIG_FILE_ERROR);
            b.append("The keyword %2% was not followed by an identifier.");
            break;

        case EC.CFG_TWICE_KEYWORD:
            b.append(CONFIG_FILE_ERROR);
            b.append("The keyword %2% appeared twice.");
            break;

        case EC.CFG_EXPECT_ID:
            b.append(CONFIG_FILE_ERROR);
            b.append("Expected an identifier after %2%.");
            break;

        case EC.CFG_GENERAL:
            b.append(CONFIG_FILE_ERROR);
            break;

        case EC.CFG_EXPECTED_SYMBOL:
            b.append(CONFIG_FILE_ERROR);
            b.append("It was expecting %2%, but did not find it.");
            break;
        case EC.CFG_ERROR_READING_FILE:
            b.append("TLC encountered the following error when trying to read the configuration file %1%:\n%2%");
            break;
        // end configuration file errors
        /* ************************************************************************ */

        case EC.GENERAL:
            // the general error adapts to the number of parameters that are passed
            for (int i = 0; i < parameters.length; i++)
            {
                b.append("%" + (i + 1) + "%"); //$NON-NLS-1$ //$NON-NLS-2$
            }
            break;
        /* 
         *  no information at all (error code wrong) 
         */
        default:
            b.append("Wrong invocation of TLC error printer. Error code not found.");
            break;
        }

        replaceString(b, parameters);
        return b.toString();
	}

    /**
     * Returns the error  
     * @param errorCode
     */
    public static String getError(int errorCode)
    {
        return getError(errorCode, EMPTY_PARAMS);
    }

    /**
     * Returns the error with one parameter 
     * @param errorCode
     * @param parameter
     */
    public static String getError(int errorCode, String parameter)
    {
        return getError(errorCode, new String[] { parameter });
    }

    /**
     * Returns parameterized error message
     * @param errorCode 
     * @param parameters a list of string parameters to be inserted into the message, by replacing 
     * %i% with the i-th parameter in the array
     */
    public static String getError(int errorCode, String[] parameters)
    {
    	recorder.record(errorCode, (Object[]) parameters);
        return getMessage(ERROR, errorCode, parameters);
    }

    /**
     * Returns the message  
     * @param errorCode
     */
    public static String getMessage(int errorCode)
    {
        return getMessage(errorCode, EMPTY_PARAMS);
    }

    /**
     * Returns the message with one parameter 
     * @param errorCode
     * @param parameter
     */
    public static String getMessage(int errorCode, String parameter)
    {
        return getMessage(errorCode, new String[] { parameter });
    }

    /**
     * Returns parameterized error message
     * @param errorCode 
     * @param parameters a list of string parameters to be inserted into the message, by replacing 
     * %i% with the i-th parameter in the array
     */
    public static String getMessage(int errorCode, String[] parameters)
    {
    	recorder.record(errorCode, (Object[]) parameters);
        return getMessage(NONE, errorCode, parameters);
    }

    /**
     * Returns TLC Bug message
     * @param errorCode
     * @return
     */
    public static String getTLCBug(int errorCode)
    {
        return getMessage(TLCBUG, errorCode, EMPTY_PARAMS);
    }

    /**
     * Prints the error for a given error code
     * @param errorCode
     */
    public static int printError(int errorCode)
    {
        return printError(errorCode, EMPTY_PARAMS);
    }

    /**
     * Prints the error with one parameter 
     * @param errorCode
     * @param parameter
     */
    public static int printError(int errorCode, String parameter)
    {
        return printError(errorCode, new String[] { parameter });
    }

    /**
     * Prints parameterized error message
     * @param errorCode 
     * @param parameters a list of string parameters to be inserted into the message, by replacing 
     * %i% with the i-th parameter in the array
     */
    public static int printError(int errorCode, String[] parameters)
    {
    	recorder.record(errorCode, (Object[]) parameters);
        // write the output
        DebugPrinter.print("entering printError(int, String[]) with errorCode " + errorCode); //$NON-NLS-1$
        ToolIO.out.println(getMessage(ERROR, errorCode, parameters));
        DebugPrinter.print("leaving printError(int, String[])"); //$NON-NLS-1$
        return errorCode;
    }

    /**
     * Prints the error by code and the provided exception.  
     * 
     * All calls of this method have includeStackTrace true.  This printing of the stack trace
     * was added in tlc2--probably by SZ.  The stack trace provides no useful information to the
     * user, so LL changed this on 20 Mar 2012 so the trace is printed only when TLC is called
     * with the -debug option. 
     * 
     * @param errorCode 
     * @param cause
     * @param includeStackTrace boolean flag if the stack-trace should be printed
     */
    private static void printError(int errorCode, String cause, Throwable throwable, boolean includeStackTrace)
    {
        printError(errorCode, cause);
        if (includeStackTrace)
        {   // Test of TLCGlobals.debug added by LL on 20 Mar 2012
            if (TLCGlobals.debug) {
              DebugPrinter.print("printing stacktrace in printError(int, Throwable, boolean)"); //$NON-NLS-1$
              throwable.printStackTrace(ToolIO.out);
        }
        }
    }

    /**
     * Prints the error by code and reports the exception message 
     * @param errorCode
     * @param cause
     */
    public static void printError(int errorCode, String[] cause, Throwable throwable)
    {
        printError(errorCode, cause);
        // Test of TLCGlobals.debug added by LL on 20 Mar 2012
        if (TLCGlobals.debug) {
            DebugPrinter.print("printing stacktrace in printError(int, Throwable, boolean)"); //$NON-NLS-1$
            throwable.printStackTrace(ToolIO.out);
        }
    }
    
    /**
     * Prints the error by code and reports the exception message
     * Modified by LL on 7 April 2012 to produce more sensible EC.GENERAL 
     * error messages.
      
     * @param errorCode
     * @param cause
     */
    public static void printError(int errorCode, String cause, Throwable throwable)
    {
        if (errorCode == EC.GENERAL) {
            printError(errorCode, ECGeneralMsg(cause, throwable));
        } else {
            printError(errorCode, cause, throwable, true);
        }
    }
    
    /**
     * Returns the error message for printError(EC.GENERAL, cause, throwable)
     * 
     * Created by LL on 7 April 2012.  
     * Modified by LL on 24 April 2012 because, for some errors,
     * throwable.getMessage() contains a nested error message, and the Toolbox's
     * code for parsing TLC output apparently cannot handle a nested error message
     * containing text before and after it.  So I put all the additional message text
     * before throwable.getMessage().
     * @param cause
     * @param throwable
     * @return
     */
    public static String ECGeneralMsg(String cause, Throwable throwable) {
        String msg = "TLC threw an unexpected exception.";
        msg = msg
                + "\nThis was probably caused by an error in the spec or model.";
        if (cause.equals("")) {
            // On 10 Nov 2012, LL added "User Output or" to the following message.
            msg = msg + "\nSee the User Output or TLC Console for clues to what happened.";
        } else {
            msg = msg + "\nThe error occurred when TLC was " + cause + ".";
        }
        if (throwable instanceof Assert.TLCRuntimeException) {
			// MK 07/25/2017: Disguise TLCRuntimeException with its parent class
			// RuntimeException to not change the externally visible TLC output 
        	// when an exception gets reports.
        	msg = msg + "\nThe exception was a " +  RuntimeException.class.getName() + "\n";
        } else {
        	msg = msg + "\nThe exception was a " +  throwable.getClass().getName() + "\n";
        }
        if (throwable.getMessage() != null) {
            msg = msg + ": " + throwable.getMessage();
            
            // Distributed TLC potentially throws exceptions unknown to the
            // Toolbox and thus not correctly reported by the Toolbox. For users
            // who want to help diagnose their problems, they can activate debug
            // output (full stack traces) in the console.  However, doing that
            // will cause some TLC errors not to be reported by the Toolbox.
            // Instead, TLC will simply halt prematurely with no error reported,
            // and the user will have to look in the console log to find out
            // what happened.
            if (DO_DEBUG) {
            	msg += throwableToString(throwable);
            }
        } else {
        	msg += throwableToString(throwable);
        }
        return msg;
    }
    
	private static String throwableToString(final Throwable e) {
		final Writer result = new StringWriter();
		final PrintWriter printWriter = new PrintWriter(result);
		e.printStackTrace(printWriter);
		return result.toString();
	}

    /**
     * Prints the error by code and reports the exception message.
     * Modified by LL on 7 April 2012 to produce more sensible EC.GENERAL 
     * error messages.
     * 
     * @param errorCode
     * @param cause
     */
    public static int printError(int errorCode, Throwable cause)
    {
        if (errorCode == EC.GENERAL) {
            printError(errorCode, "", cause);
        } else {
            printError(errorCode, cause.getMessage(), cause, true);
        }
        return errorCode;
    }

    /**
     * Prints the error for a given error code
     * @param errorCode
     */
    public static void printMessage(int errorCode)
    {
        printMessage(errorCode, EMPTY_PARAMS);
    }

    /**
     * Prints the error with one parameter 
     * @param errorCode
     * @param parameter
     */
    public static void printMessage(int errorCode, String parameter)
    {
        printMessage(errorCode, new String[] { parameter });
    }

    /**
     * Prints parameterized error message
     * @param errorCode 
     * @param parameters a list of string parameters to be inserted into the message, by replacing 
     * %i% with the i-th parameter in the array
     */
    public static void printMessage(int errorCode, String... parameters)
    {
    	recorder.record(errorCode, (Object[]) parameters);
        DebugPrinter.print("entering printMessage(int, String[]) with errorCode " + errorCode); //$NON-NLS-1$
        // write the output
		ToolIO.out.println(getMessage(NONE, errorCode, parameters));
		// Don't log the start and end markers when in -tool mode.
		TLAFlightRecorder.message(getMessage0(NONE, errorCode, parameters));
        DebugPrinter.print("leaving printError(int, String[]) with errorCode "); //$NON-NLS-1$
    }

    public static int printTLCRuntimeException(final TLCRuntimeException tre) {
    	if (tre.parameters != null) {
    		recorder.record(tre.errorCode, (Object[]) new Object[] {tre});
    		DebugPrinter.print("entering printTLCRuntimeException(TLCRuntimeException) with errorCode " + tre.errorCode); //$NON-NLS-1$
    		// write the output
    		ToolIO.out.println(getMessage(ERROR, tre.errorCode, tre.parameters));
    		DebugPrinter.print("leaving printTLCRuntimeException(TLCRuntimeException) with errorCode "); //$NON-NLS-1$
    	} else {
    		// Legacy code path except actual errorCode instead of EC.General.
    		printError(tre.errorCode, tre);
    	}
    	return tre.errorCode;
    }
    
    /** 
     * Prints the state
     * @param parameters
     */
    public static void printState(int code, String[] parameters, TLCState state, int num)
    {
		recorder.record(code, new TLCStateInfo(state, ""), num);
        DebugPrinter.print("entering printState(String[])"); //$NON-NLS-1$
        ToolIO.out.println(getMessage(STATE, code, parameters));
        DebugPrinter.print("leaving printState(String[])"); //$NON-NLS-1$
    }
    
    public static void printState(int code, String[] parameters, TLCStateInfo stateInfo, int num)
    {
		recorder.record(code, (TLCStateInfo) stateInfo, num);
        DebugPrinter.print("entering printState(String[])"); //$NON-NLS-1$
        ToolIO.out.println(getMessage(STATE, code, parameters));
        DebugPrinter.print("leaving printState(String[])"); //$NON-NLS-1$
    }

    /**
     * Prints parameterized TLC BUG message
     * @param errorCode 
     * @param parameters a list of string parameters to be inserted into the message, by replacing 
     * %i% with the i-th parameter in the array
     */
    public static void printTLCBug(int errorCode, String[] parameters)
    {
    	recorder.record(errorCode, (Object[]) parameters);
        DebugPrinter.print("entering printTLCBug(int, String[]) with errorCode " + errorCode); //$NON-NLS-1$
        // write the output
        ToolIO.out.println(getMessage(TLCBUG, errorCode, parameters));
        DebugPrinter.print("leaving printTLCBug(int, String[])"); //$NON-NLS-1$
    }

    /**
     * @see MP#printWarning(int)
     */
	public static void printWarning(final int errorCode) {
		printWarning(errorCode, new String[0]);
	}

    /**
     * @see MP#printWarning(int, String[])
     */
	public static void printWarning(final int errorCode, final String parameter) {
		printWarning(errorCode, new String[] {parameter});
	}
	
    /**
     * Prints a warning (if the global switch is enabled and it is not a duplicate warning)
     * @param errorCode
     * @param parameters
     */
    public static void printWarning(int errorCode, String... parameters)
    {
    	recorder.record(errorCode, (Object[]) parameters);
        DebugPrinter.print("entering printWarning(int, String[]) with errorCode " + errorCode); //$NON-NLS-1$
        // only print warnings if the global warning switch was enabled
        if (TLCGlobals.warn)
        {
            // construct the message
            String message = getMessage(WARNING, errorCode, parameters);
            // if the message has not been printed
            if (instance.warningHistory.put(message) == null)
            {
                // print it
                ToolIO.out.println(message);
            }
        }
        DebugPrinter.print("leaving printWarning(int, String[])"); //$NON-NLS-1$
    }
    
    /**
     * Prints a warning (if the global switch is enabled and it is not a duplicate warning)
     * @param errorCode
     * @param parameters
     */
    public static void printWarning(int errorCode, String parameters, Throwable e)
    {
    	recorder.record(errorCode, parameters, e);
        DebugPrinter.print("entering printWarning(int, String, Exception) with errorCode " + errorCode); //$NON-NLS-1$
        // only print warnings if the global warning switch was enabled
        if (TLCGlobals.warn)
        {
            // construct the message
            String message = getMessage(WARNING, errorCode, new String[]{parameters});
            // if the message has not been printed
            if (instance.warningHistory.put(message) == null)
            {
                // print it
                ToolIO.out.println(message);
            }
            DebugPrinter.print("printing stacktrace in printError(int, Throwable, boolean)"); //$NON-NLS-1$
            e.printStackTrace(ToolIO.out);
        }
        DebugPrinter.print("leaving printWarning(int, String[])"); //$NON-NLS-1$
    }
    
    public static void printStats(final IBucketStatistics inDegree, final IBucketStatistics outDegree) {
    	// Out degree
        ToolIO.out.println(outDegree);
        
        // In Degree
		ToolIO.out.println(inDegree);

		// SCC size and count
		ToolIO.out.println(LiveWorker.STATS.toString());
		ToolIO.out.println(String.format("%s SCC%s found during liveness checking.",
				LiveWorker.STATS.getObservations(), LiveWorker.STATS.getObservations() > 1 ? "s" : ""));
    }

    /**
     * Replaces the place holders by parameters 
     */
    public static StringBuffer replaceString(StringBuffer buffer, String[] parameters)
    {
        // replace parameters, if any
        int placeHolderPosition = -1;
        String placeHolder = null;
        // replace all parameters
        for (int i = 0; i < parameters.length; i++)
        {
            if (parameters[i] == null)
            {
                break;
            }
            placeHolder = "%" + (i + 1) + "%"; //$NON-NLS-1$ //$NON-NLS-2$
            placeHolderPosition = buffer.indexOf(placeHolder);
            if (placeHolderPosition != -1)
            {
                buffer.replace(placeHolderPosition, placeHolderPosition + placeHolder.length(), parameters[i]);
            } else
            {
                // the place holder is not found
                // stop processing
                break;
            }
        }

        return buffer;
    }

    /**
     * Flushes the output buffers
     */
    public static void flush()
    {
        ToolIO.out.flush();
        ToolIO.err.flush();
    }

	public static void setRecorder(MPRecorder aRecorder) {
		recorder = aRecorder;
	}

    private static String now() {
    	if (Boolean.getBoolean(MP.class.getName() + ".noTimestamps")) {
			// Return NOW if requested by setting -Dtlc2.output.MP.noTimestamps=true on the
			// command-line. Can be useful if one wants to compare TLC's output from
			// multiple executions.
    		return "NOW";
    	}
		return SDF.format(new Date());
	}

	public static String format(final long l) {
		return df.format(l);
	}
}
