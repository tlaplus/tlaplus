package tlc2.output;

import util.ToolIO;

/**
 * Error message printer
 * @author Simon Zambrovski
 * @version $Id$
 */
public class MP
{
    private static final String[] EMPTY_PARAMS = new String[0];

    private static final int NONE = 0;
    private static final int ERROR = 1;
    private static final int TLCBUG = 2;

    /**
     * Returns the formatted message
     * @param messageClass one of ERROR, TLCBUG
     * @param messageCode see ErrorCodes class
     * @param parameters string of parameters to be replaced in the message
     * @return the formatted message
     */
    private static String getMessage(int messageClass, int messageCode, String[] parameters)
    {
        if (parameters == null)
        {
            parameters = EMPTY_PARAMS;
        }

        StringBuffer b = new StringBuffer();

        // depending on message class add different prefix
        switch (messageClass) {
        case ERROR:
            b.append("Error: ");
            break;
        case TLCBUG:
            b.append("TLC Bug: ");
            break;
        case NONE:
        default:
            break;
        }

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

        case EC.WRONG_COMMANDLINE_PARAMS_TLC:
            b.append("%1%\nUsage: java tlc2.TLC [-option] inputfile");
            break;
        case EC.WRONG_COMMANDLINE_PARAMS_SIMULATOR:
            b.append("%1%\nUsage: java tlc2.Simulator [-option] inputfile");
            break;

        case EC.SYSTEM_OUT_OF_MEMORY_TOO_MANY_INIT:
            b.append("Out Of Memory. There are probably too many initial states.");
            break;

        case EC.TLC_PP_FORMATING_VALUE:
            b.append("error while formating %1%\n%2%");
            break;

        case EC.TLC_PP_PARSING_VALUE:
            b.append("error while parsing %1%\n%2%");
            break;

        case EC.TLC_METADIR_EXISTS:
            b.append("TLC writes its files to a directory whose name is generated"
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

        case EC.TLC_ASSUMPTION_EVALUATION_ERROR:
            b.append("Evaluating assumption %1% failed.\n%2%");
            break;
        case EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_INITIAL:
            b.append("State is not completely specified by the " + "initial predicate:\n%2%");
            break;
        case EC.TLC_INVARIANT_VIOLATED_INITIAL:
            b.append("Invariant %1% is violated by the initial state:\n%2%");
            break;
        case EC.TLC_PROPERTY_VIOLATED_INITIAL:
            b.append("Property %1% is violated by the initial state:\n%2%");
            break;

        case EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT:
            b.append("Successor state is not completely specified by the" + " next-state action.\n");
            break;
        case EC.TLC_INVARIANT_VIOLATED_BEHAVIOR:
            b.append("Invariant %1% is violated.");
            break;

        case EC.TLC_INVARIANT_EVALUATION_FAILED:
            b.append("Evaluating invariant %1% failed.");
            break;

        case EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR:
            b.append("Error: Action property %1%" + " is violated.");
            break;

        case EC.TLC_ACTION_PROPERTY_EVALUATION_FAILED:
            b.append("Evaluating action property %1% failed.");
            break;

        case EC.TLC_DEADLOCK_REACHED:
            b.append("Deadlock reached.");
            break;

        case EC.TLC_TEMPORAL_PROPERTY_VIOLATED:
            b.append("Temporal properties were violated.\n"
                    + "The following behaviour constitutes a counter-example:\n");
            break;

        case EC.TLC_FAILED_TO_RECOVER_NEXT:
            b.append("Failed to recover the next state from its fingerprint.");
            break;

        case EC.TLC_FAILED_TO_RECOVER_INIT:
            b.append("Failed to recover the initial state from its fingerprint.");
            break;

        case EC.TLC_NO_STATES_SATISFYING_INIT:
            b.append("There is no state satisfying the initial state predicate.");
            break;

        case EC.TLC_STRING_MODULE_NOT_FOUND:
            b.append("This is a TLC bug: TLC could not find its built-in String module.\n");
            break;

        case EC.TLC_BACK_TO_STATE:
            b.append("Back to state %1%.\n");
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

        case EC.SYSTEM_ERROR_READING_POOL:
            b.append("when reading the disk (StatePoolReader.run):\n%1%");
            break;

        case EC.SYSTEM_CHECKPOINT_RECOVERY_CORRUPT:
            b.append("TLC encountered the following error while restarting from a "
                    + "checkpoint;\n the checkpoint file is probably corrupted.\n%1%");
            break;
            
            
        case EC.SYSTEM_ERROR_WRITING_POOL:
            b.append("Error: when writing the disk (StatePoolWriter.run):\n%1%");
            break;
            
            
            
            
            
            
            
            

        /* 
         *  no information at all 
         */
        case EC.GENERAL:
        default:
            break;
        }

        // replace parameters, if any
        int placeHolderPosition = -1;
        String placeHolder = null;
        // replace all parameters
        for (int i = 0; i < parameters.length; i++)
        {
            placeHolder = "%" + (i + 1) + "%";
            placeHolderPosition = b.indexOf(placeHolder);
            if (placeHolderPosition != -1)
            {
                b.replace(placeHolderPosition, placeHolderPosition + placeHolder.length(), parameters[i]);
            } else
            {
                // the place holder is not found
                // stop processing
                break;
            }
        }
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
    public static void printError(int errorCode)
    {
        printError(errorCode, EMPTY_PARAMS);
    }

    /**
     * Prints the error with one parameter 
     * @param errorCode
     * @param parameter
     */
    public static void printError(int errorCode, String parameter)
    {
        printError(errorCode, new String[] { parameter });
    }

    /**
     * Prints parameterized error message
     * @param errorCode 
     * @param parameters a list of string parameters to be inserted into the message, by replacing 
     * %i% with the i-th parameter in the array
     */
    public static void printError(int errorCode, String[] parameters)
    {
        // write the output
        ToolIO.err.println(getMessage(ERROR, errorCode, parameters));
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
    public static void printMessage(int errorCode, String[] parameters)
    {
        // write the output
        ToolIO.err.println(getMessage(NONE, errorCode, parameters));
    }

    /**
     * Prints parameterized TLC BUG message
     * @param errorCode 
     * @param parameters a list of string parameters to be inserted into the message, by replacing 
     * %i% with the i-th parameter in the array
     */
    public static void printTLCBug(int errorCode, String[] parameters)
    {
        // write the output
        ToolIO.err.println(getMessage(TLCBUG, errorCode, parameters));
    }

}
