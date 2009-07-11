package tlc2.output;

/**
 * Interface containing the error code constants 
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface EC
{
    public final static int UNIT_TEST = -123456;
    
    public static final int GENERAL = 1000;
    public static final int SYSTEM_OUT_OF_MEMORY = 1001;
    public static final int SYSTEM_OUT_OF_MEMORY_TOO_MANY_INIT = 1002;
    public static final int SYSTEM_STACK_OVERFLOW = 1005;

    public static final int WRONG_COMMANDLINE_PARAMS_SIMULATOR = 1101;
    public static final int WRONG_COMMANDLINE_PARAMS_TLC = 1102;
    
    public static final int TLC_PP_PARSING_VALUE = 2000;
    public static final int TLC_PP_FORMATING_VALUE = 2001;
    
    public static final int TLC_METADIR_EXISTS = 2100;
    public static final int TLC_METADIR_CAN_NOT_BE_CREATED = 2101;
    public static final int TLC_INITIAL_STATE = 2102;
    public static final int TLC_NESTED_EXPRESSION = 2103;
    public static final int TLC_ASSUMPTION_FALSE = 2104;
    public static final int TLC_ASSUMPTION_EVALUATION_ERROR = 2105;
    public static final int TLC_STATE_NOT_COMPLETELY_SPECIFIED_INITIAL = 2106;

    public static final int TLC_INVARIANT_VIOLATED_INITIAL = 2107;
    public static final int TLC_PROPERTY_VIOLATED_INITIAL = 2108;
    public static final int TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT = 2109;
    public static final int TLC_INVARIANT_VIOLATED_BEHAVIOR = 2110;
    public static final int TLC_INVARIANT_EVALUATION_FAILED = 2111;
    public static final int TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR = 2112;
    public static final int TLC_ACTION_PROPERTY_EVALUATION_FAILED = 2113;
    public static final int TLC_DEADLOCK_REACHED = 2114;
    
    public static final int TLC_TEMPORAL_PROPERTY_VIOLATED = 2116;
    public static final int TLC_FAILED_TO_RECOVER_NEXT = 2117;
    public static final int TLC_NO_STATES_SATISFYING_INIT = 2118;
    public static final int TLC_STRING_MODULE_NOT_FOUND = 2119;
    
    public static final int TLC_ERROR_STATE = 2120;
    public static final int TLC_BEHAVIOR_UP_TO_THIS_POINT = 2121;

    public static final int TLC_BACK_TO_STATE = 2122;

    public static final int TLC_FAILED_TO_RECOVER_INIT = 2123;

    public static final int TLC_REPORTER_DIED = 2124;

    public static final int SYSTEM_ERROR_READING_POOL = 2125;

    public static final int SYSTEM_CHECKPOINT_RECOVERY_CORRUPT = 2126;

    public static final int SYSTEM_ERROR_WRITING_POOL = 2127;
}
