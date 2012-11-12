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

    
    public final static int SANY_PARSER_CHECK_1 = 4000;
    public final static int SANY_PARSER_CHECK_2 = 4001;
    public final static int SANY_PARSER_CHECK_3 = 4002;

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
    public static final int TLC_BACK_TO_STATE = 2122;  // The "back to state" message from a liveness-error trace.
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
    public static final int TLC_PARAMETER_MUST_BE_POSTFIX = 2136; 
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
    /** Simon used an argument like "\bn apple" to TLC_MODULE_ARGUMENT_ERROR to turn
     * an "a" into an "an".  This doesn't work on the Toolbox's console.  Hence, LL added
     * the following message type on 21 May 2012. */
    public static final int TLC_MODULE_ARGUMENT_ERROR_AN = 2266;
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
    
    public static final int TLC_STARTING = 2185;
    public static final int TLC_FINISHED = 2186;
    
    // distributed TLC
    
    public static final int TLC_DISTRIBUTED_SERVER_RUNNING = 7000;
    public static final int TLC_DISTRIBUTED_WORKER_REGISTERED = TLC_DISTRIBUTED_SERVER_RUNNING + 1;
    public static final int TLC_DISTRIBUTED_WORKER_DEREGISTERED = TLC_DISTRIBUTED_WORKER_REGISTERED + 1;
    public static final int TLC_DISTRIBUTED_WORKER_STATS = TLC_DISTRIBUTED_WORKER_DEREGISTERED + 1;
    public static final int TLC_DISTRIBUTED_SERVER_NOT_RUNNING = TLC_DISTRIBUTED_WORKER_STATS + 1;
    public static final int TLC_DISTRIBUTED_VM_VERSION = TLC_DISTRIBUTED_SERVER_NOT_RUNNING + 1;
    public static final int TLC_DISTRIBUTED_WORKER_LOST = TLC_DISTRIBUTED_VM_VERSION + 1;
    public static final int TLC_DISTRIBUTED_EXCEED_BLOCKSIZE = TLC_DISTRIBUTED_WORKER_LOST + 1;
    public static final int TLC_DISTRIBUTED_SERVER_FPSET_WAITING = TLC_DISTRIBUTED_EXCEED_BLOCKSIZE + 1;
    public static final int TLC_DISTRIBUTED_SERVER_FPSET_REGISTERED = TLC_DISTRIBUTED_SERVER_FPSET_WAITING + 1;
    public static final int TLC_DISTRIBUTED_SERVER_FINISHED = TLC_DISTRIBUTED_SERVER_FPSET_REGISTERED + 1;
    
    // errors during parsing of the model configuration
    
    public static final int CFG_ERROR_READING_FILE = 5001;
    public static final int CFG_GENERAL = 5002;
    public static final int CFG_MISSING_ID = 5003;
    public static final int CFG_TWICE_KEYWORD = 5004;
    public static final int CFG_EXPECT_ID = 5005;
    public static final int CFG_EXPECTED_SYMBOL = 5006;
    public static final int TLC_MODE_MC = 2187;
    public static final int TLC_MODE_SIMU = 2188;
    public static final int TLC_COMPUTING_INIT = 2189;
    public static final int TLC_INIT_GENERATED1 = 2190;
    public static final int TLC_INIT_GENERATED2 = 2191;
    public static final int TLC_INIT_GENERATED3 = 2207;
    public static final int TLC_INIT_GENERATED4 = 2208;
    public static final int TLC_CHECKING_TEMPORAL_PROPS = 2192;
    public static final int TLC_SUCCESS = 2193;
    public static final int TLC_SEARCH_DEPTH = 2194;
    public static final int TLC_CHECKPOINT_START = 2195;
    public static final int TLC_CHECKPOINT_END = 2196;
    public static final int TLC_CHECKPOINT_RECOVER_START = 2197;
    public static final int TLC_CHECKPOINT_RECOVER_END = 2198;
    public static final int TLC_STATS = 2199;
    public static final int TLC_STATS_DFID = 2204;
    public static final int TLC_STATS_SIMU = 2210;
    public static final int TLC_PROGRESS_STATS = 2200;
    public static final int TLC_COVERAGE_START = 2201;
    public static final int TLC_COVERAGE_END = 2202;
    public static final int TLC_CHECKPOINT_RECOVER_END_DFID = 2203;
    public static final int TLC_PROGRESS_START_STATS_DFID = 2205;
    public static final int TLC_PROGRESS_STATS_DFID = 2206;
    public static final int TLC_PROGRESS_SIMU = 2209;
    public static final int TLC_FP_COMPLETED = 2211;
    
    public static final int TLC_LIVE_IMPLIED = 2212;
    public static final int TLC_LIVE_CANNOT_HANDLE_FORMULA = 2213;
    public static final int TLC_LIVE_WRONG_FORMULA_FORMAT = 2214;
    public static final int TLC_LIVE_ENCOUNTERED_ACTIONS = 2249;
    public static final int TLC_LIVE_STATE_PREDICATE_NON_BOOL = 2250;
    public static final int TLC_LIVE_CANNOT_EVAL_FORMULA = 2251;
    public static final int TLC_LIVE_ENCOUNTERED_NONBOOL_PREDICATE = 2252;

    
    public static final int TLC_EXPECTED_VALUE = 2215;
    public static final int TLC_EXPECTED_EXPRESSION = 2246;
    public static final int TLC_EXPECTED_EXPRESSION_IN_COMPUTING = 2247;
    public static final int TLC_EXPECTED_EXPRESSION_IN_COMPUTING2 = 2248;
    
    
    // state printing
    public static final int TLC_STATE_PRINT1 = 2216;
    public static final int TLC_STATE_PRINT2 = 2217;
    public static final int TLC_STATE_PRINT3 = 2218;  // This seems to be a "Stuttering" message from a liveness-error trace 
    public static final int TLC_SANY_END = 2219;
    public static final int TLC_SANY_START = 2220;
    public static final int TLC_COVERAGE_VALUE = 2221;
    
    // config file errors
    public static final int TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM = 2222;
    public static final int TLC_CONFIG_RHS_ID_APPEARED_AFTER_LHS_ID = 2223;
    public static final int TLC_CONFIG_WRONG_SUBSTITUTION = 2224;
    public static final int TLC_CONFIG_WRONG_SUBSTITUTION_NUMBER_OF_ARGS = 2225;
    public static final int TLC_CONFIG_ID_DOES_NOT_APPEAR_IN_SPEC = 2226;
    public static final int TLC_CONFIG_NOT_BOTH_SPEC_AND_INIT = 2227;
    public static final int TLC_CONFIG_ID_REQUIRES_NO_ARG = 2228;
    public static final int TLC_CONFIG_SPECIFIED_NOT_DEFINED = 2229;
    public static final int TLC_CONFIG_ID_HAS_VALUE = 2230;
    public static final int TLC_CONFIG_MISSING_INIT = 2231;
    public static final int TLC_CONFIG_MISSING_NEXT = 2232;
    public static final int TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT = 2233;
    public static final int TLC_CONFIG_OP_NO_ARGS = 2234;
    public static final int TLC_CONFIG_OP_NOT_IN_SPEC = 2235;
    public static final int TLC_CONFIG_OP_IS_EQUAL = 2236;
    public static final int TLC_CONFIG_SPEC_IS_TRIVIAL = 2237;
    public static final int TLC_CANT_HANDLE_SUBSCRIPT = 2238;
    public static final int TLC_CANT_HANDLE_CONJUNCT = 2239;
    public static final int TLC_CANT_HANDLE_TOO_MANY_NEXT_STATE_RELS = 2240;
    public static final int TLC_CONFIG_PROPERTY_NOT_CORRECTLY_DEFINED = 2241;
    public static final int TLC_CONFIG_OP_ARITY_INCONSISTENT = 2242;
    public static final int TLC_CONFIG_NO_STATE_TYPE = 2243;
    public static final int TLC_CANT_HANDLE_REAL_NUMBERS = 2244;
    public static final int TLC_NO_MODULES = 2245;
    
    public static final int TLC_ENABLED_WRONG_FORMULA = 2260;
    public static final int TLC_ENCOUNTERED_FORMULA_IN_PREDICATE = 2261;
    public static final int TLC_VERSION = 2262;
    public static final int TLC_USAGE = 2263;
    public static final int TLC_COUNTER_EXAMPLE = 2264;
    
    public static final int TLC_INTEGER_TOO_BIG = 2265;
}
