package tlc2.output;


/**
 * Interface containing the error code constants 
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface EC
{
    // Check and CheckImpl
    // check if the TLC option is the same for params
    public static final int CHECK_FAILED_TO_CHECK = 3000;
    public static final int CHECK_COULD_NOT_READ_TRACE = 3001;

    public static final int CHECK_PARAM_EXPECT_CONFIG_FILENAME = 3100;
    public static final int CHECK_PARAM_USAGE = 3101;
    public static final int CHECK_PARAM_MISSING_TLA_MODULE = 3102;
    public static final int CHECK_PARAM_NEED_TO_SPECIFY_CONFIG_DIR = 3103;
    public static final int CHECK_PARAM_WORKER_NUMBER_REQUIRED = 3104;
    public static final int CHECK_PARAM_WORKER_NUMBER_TOO_SMALL = 3105;
    public static final int CHECK_PARAM_WORKER_NUMBER_REQUIRED2 = 3106;
    public static final int CHECK_PARAM_DEPTH_REQUIRED = 3107;
    public static final int CHECK_PARAM_DEPTH_REQUIRED2 = 3108;
    public static final int CHECK_PARAM_TRACE_REQUIRED = 3109;
    public static final int CHECK_PARAM_COVREAGE_REQUIRED = 3110;
    public static final int CHECK_PARAM_COVREAGE_REQUIRED2 = 3111;
    public static final int CHECK_PARAM_COVREAGE_TOO_SMALL = 3112;
    public static final int CHECK_PARAM_UNRECOGNIZED = 3113;
    public static final int CHECK_PARAM_TOO_MANY_INPUT_FILES = 3114;

    
    public final static int SANY_PARSER_CHECK = 4000;

    public static final int UNKNOWN = -1;  // TODO remove all these
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
    public static final int SYSTEM_INDEX_ERROR = 2134;
    public static final int SYSTEM_STREAM_EMPTY = 2135;
    public static final int SYSTEM_FILE_NULL = 2137;
    public static final int SYSTEM_INTERRUPTED = 2138;
    public static final int SYSTEM_UNABLE_NOT_RENAME_FILE = 2160;
    public static final int SYSTEM_DISK_IO_ERROR_FOR_FILE = 2161;
    public static final int SYSTEM_METADIR_EXISTS = 2162;
    public static final int SYSTEM_METADIR_CREATION_ERROR = 2163;
    public static final int SYSTEM_UNABLE_TO_OPEN_FILE = 2167;
    public static final int TLC_BUG = 2128; // TODO Bad description

    public static final int SYSTEM_DISKGRAPH_ACCESS = 2129; // TODO refactor  

    public static final int TLC_AAAAAAA = 2130;
    public static final int TLC_REGISTRY_INIT_ERROR = 2131;
    public static final int TLC_CHOOSE_ARGUMENTS_WRONG = 2164;
    public static final int TLC_CHOOSE_UPPER_BOUND = 2165;

    public static final int TLC_VALUE_ASSERT_FAILED = 2132;
    public static final int TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE = 2154;

    public static final int TLC_FP_NOT_IN_SET = 2133;
    public static final int TLC_FP_VALUE_ALREADY_ON_DISK = 2166;

    public static final int TLC_LIVE_BEGRAPH_FAILED_TO_CONSTRUCT = 2159;
    public static final int TLC_PARAMETER_MUST_BE_POSTFIX = 2136; // TODO Check this message
    public static final int TLC_COULD_NOT_DETERMINE_SUBSCRIPT = 2139;
    public static final int TLC_SUBSCRIPT_CONTAIN_NO_STATE_VAR = 2140;
    public static final int TLC_WRONG_TUPLE_FIELD_NAME = 2141;
    public static final int TLC_WRONG_RECORD_FIELD_NAME = 2142;
    public static final int TLC_UNCHANGED_VARIABLE_CHANGED = 2143;
    public static final int TLC_EXCEPT_APPLIED_TO_UNKNOWN_FIELD = 2144;

    public static final int TLC_MODULE_TLCGET_UNDEFINED = 2145;
    /** Attempted to compare %1% with the value\n%2% */
    public static final int TLC_MODULE_COMPARE_VALUE = 2155;
    public static final int TLC_MODULE_CHECK_MEMBER_OF = 2158;
    public static final int TLC_MODULE_TRANSITIVE_CLOSURE = 2157;
    /** The %1% argument of %2% should be a %3%, but instead it is:<br>%4% */
    public static final int TLC_MODULE_ARGUMENT_ERROR = 2169;
    public static final int TLC_ARGUMENT_MISMATCH = 2170;
    public static final int TLC_PARSING_FAILED2 = 2171;
    public static final int TLC_PARSING_FAILED = 3002;
    public static final int TLC_TOO_MNY_POSSIBLE_STATES = 2172;
    public static final int TLC_ERROR_REPLACING_MODULES = 2173;
    public static final int SYSTEM_ERROR_READING_STATES = 2174;
    public static final int SYSTEM_ERROR_WRITING_STATES = 2175;
    public static final int TLC_MODULE_APPLYING_TO_WRONG_VALUE = 2176;
    public static final int TLC_MODULE_BAG_UNION1 = 2177;
    public static final int TLC_MODULE_OVERFLOW = 2178;
    public static final int TLC_MODULE_DIVISION_BY_ZERO = 2179;
    public static final int TLC_MODULE_NULL_POWER_NULL = 2180;
    public static final int TLC_MODULE_COMPUTING_CARDINALITY = 2181;
    public static final int TLC_MODULE_EVALUATING = 2182;
    /** The %1% argument of %2% must be in the domain of its first argument:<br>%3%<br>, but instead it is<br>%4% */
    public static final int TLC_MODULE_ARGUMENT_NOT_IN_DOMAIN = 2183;
    public static final int TLC_MODULE_APPLY_EMPTY_SEQ = 2184;
    
    
    // errors during parsing of the model configuration
    
    public static final int CFG_ERROR_READING_FILE = 5001;
    public static final int CFG_GENERAL = 5002;
    public static final int CFG_MISSING_ID = 5003;
    public static final int CFG_TWICE_KEYWORD = 5004;
    public static final int CFG_EXPECT_ID = 5005;
    public static final int CFG_EXPECTED_SYMBOL = 5006;
    

}
