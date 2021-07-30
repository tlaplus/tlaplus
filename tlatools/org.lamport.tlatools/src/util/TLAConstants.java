package util;

/**
 * A class of bits of keywords, operators, and bears.
 */
public final class TLAConstants {
	public final class ANSI {
		public static final String BOLD_CODE = "\033[1m";
		public static final String ITALIC_CODE = "\033[3m";
		public static final String RESET_CODE = "\033[0m";
	}
	
	public final class BuiltInModules {
		public static final String TLC = "TLC";
		public static final String TRACE_EXPRESSIONS = "Toolbox";
	}
	
	public final class BuiltInOperators {
		public static final String PERMUTATIONS = "Permutations";
	}
	
	public final class Files {
	    public static final String CONFIG_EXTENSION = ".cfg";
	    public static final String ERROR_EXTENSION = ".err";
	    public static final String OUTPUT_EXTENSION = ".out";
	    public static final String TLA_EXTENSION = ".tla";
		
		public static final String MODEL_CHECK_FILE_BASENAME = "MC";
		public static final String MODEL_CHECK_CONFIG_FILE = MODEL_CHECK_FILE_BASENAME + CONFIG_EXTENSION;
		public static final String MODEL_CHECK_ERROR_FILE = MODEL_CHECK_FILE_BASENAME + ERROR_EXTENSION;
		public static final String MODEL_CHECK_OUTPUT_FILE = MODEL_CHECK_FILE_BASENAME + OUTPUT_EXTENSION;
		public static final String MODEL_CHECK_TLA_FILE = MODEL_CHECK_FILE_BASENAME + TLA_EXTENSION;
	}
	
	public final class KeyWords {
		public static final String ACTION_CONSTRAINT = "ACTION_CONSTRAINT";
		public static final String ASSUME = "ASSUME";
	    public static final String CONSTANT = "CONSTANT";
	    public static final String CONSTANTS = CONSTANT + 'S';
	    public static final String EXTENDS = "EXTENDS";
	    public static final String INIT = "INIT";
	    public static final String INVARIANT = "INVARIANT";
	    public static final String MODULE = "MODULE";
	    public static final String NEXT = "NEXT";
	    public static final String PROPERTY = "PROPERTY";
	    public static final String SPECIFICATION = "SPECIFICATION";
	    public static final String SYMMETRY = "SYMMETRY";
	    public static final String TRUE = "TRUE";
	    public static final String UNION = "\\union";
	    public static final String VARIABLE = "VARIABLE";
	    public static final String ENABLED = "ENABLED";
	    public static final String VIEW = "VIEW";
	}
	
	public final class LoggingAtoms {
		public static final String PARSING_FILE = "Parsing file";
	}
    
	public final class Schemes {
		public static final String SPEC_SCHEME = "spec";
		public static final String INIT_SCHEME = "init";
		public static final String NEXT_SCHEME = "next";
		public static final String CONSTANT_SCHEME = "const";
		public static final String SYMMETRY_SCHEME = "symm";
		public static final String DEFOV_SCHEME = "def_ov";
		public static final String CONSTRAINT_SCHEME = "constr";
		public static final String ACTIONCONSTRAINT_SCHEME = "action_constr";
		public static final String INVARIANT_SCHEME = "inv";
		public static final String PROP_SCHEME = "prop";
		public static final String VIEW_SCHEME = "view";
		public static final String POST_CONDITION_SCHEME = "postcondition";
		public static final String ALIAS_SCHEME = "alias";
		public static final String CONSTANTEXPR_SCHEME = "const_expr";
		public static final String TRACE_EXPR_VAR_SCHEME = "__trace_var";
		public static final String TRACE_EXPR_DEF_SCHEME = "trace_def";
	}
	
	public final class TraceExplore {
	    public static final String TRACE_EXPRESSION_MODULE_NAME = "TTrace";
	    public static final String ERROR_STATES_MODULE_NAME = "TraceDef";
	    public static final String EXPLORATION_MODULE_NAME = "TEExpression";
		public static final String ACTION = "_TEAction";
		public static final String POSITION = "_TEPosition";
		public static final String TRACE = "_TETrace";
	    /**
	     * expressions to be evaluated at each state of the trace
	     * when the trace explorer is run
	     */
	    public static final String TRACE_EXPLORE_EXPRESSIONS = "traceExploreExpressions";
	    /**
	     * Conjunction of variable values in the initial state of a trace
	     * Should only include spec variables, not trace expression variables.
	     */
	    public static final String TRACE_EXPLORE_INIT = "traceExploreInit";
	    /**
	     * Disjunction of actions used for trace exploration without the trace
	     * expression variables.
	     */
	    public static final String TRACE_EXPLORE_NEXT = "traceExploreNext";
	    /**
	     * The tuple of ordered sub-action names representing the trace states. 
	     */
	    public static final String TRACE_EXPLORE_ACTION_CONSTRAINT = "traceExploreActionConstraint";
	    public static final String SPEC_TE_TRACE_EXPRESSION = "expression";
	    public static final String SPEC_TE_TTRACE_EXPRESSION = "_expression";
		public static final String SPEC_TETRACE_TRACE_DEF = "trace";
		public static final String SPEC_TETRACE_TRACE = "_trace";
		public static final String SPEC_TETRACE_NAME = "TETrace";
		public static final String SPEC_TECONSTANTS_NAME = "TEConstants";
		public static final String SPEC_TE_INIT = "_init";
		public static final String SPEC_TE_CONSTRAINT = "_constraint";
		public static final String SPEC_TE_NEXT = "_next";
		public static final String SPEC_TETRACE_LASSO_START = "_TTraceLassoStart";
		public static final String SPEC_TETRACE_LASSO_END = "_TTraceLassoEnd";
		public static final String VIEW = "_view";
	}

	
	public static final String BACK_TO_STATE = "Back to state";
	public static final String GENERATION_TIMESTAMP_PREFIX = "\\* Generated on ";
	public static final String LINE = "line ";
	public static final String STUTTERING = " Stuttering";
	
	public static final String MODULE_OPENING_PREFIX_REGEX = "^([-]+ " + TLAConstants.KeyWords.MODULE + ") ";
	public static final String MODULE_CLOSING_REGEX = "^[=]+$";

    public static final String SPACE = " ";
    public static final String INDENT = "    ";
    public static final String CR = "\n";
    public static final String SEP = "----";
    public static final String EQ = " = ";
    public static final String ARROW = " <- ";
    public static final String RECORD_ARROW = " |-> ";
    public static final String DEFINES = " == ";
    public static final String DEFINES_CR = " ==\n";
    public static final String COMMENT_NS = "\\*";
    public static final String COMMENT = COMMENT_NS + SPACE;
    public static final String ATTRIBUTE = "@";
    public static final String COLON = ":";
    public static final String EMPTY_STRING = "";
    public static final String CONSTANT_EXPRESSION_EVAL_IDENTIFIER = "\"$!@$!@$!@$!@$!\"";
    public static final String COMMA = ",";
    public static final String BEGIN_TUPLE = "<<";
    public static final String END_TUPLE = ">>";
    public static final String PRIME = "'";
    public static final String QUOTE = "\"";
    public static final String TLA_AND = "/\\";
    public static final String TLA_OR = "\\/";
    public static final String TLA_NOT = "~";
    public static final String TLA_EVENTUALLY_ALWAYS = "<>[]";
    public static final String TLA_INF_OFTEN = "[]<>";
    public static final String TRACE_NA = "\"--\"";
    public static final String L_PAREN = "(";
    public static final String R_PAREN = ")";
    public static final String L_SQUARE_BRACKET = "[";
    public static final String R_SQUARE_BRACKET = "]";
    public static final String FALSE = "FALSE";
    public static final String TRUE = "TRUE";

    public static final String INDENTED_CONJUNCTIVE = TLAConstants.INDENT + TLAConstants.TLA_AND + TLAConstants.SPACE;
    public static final String INDENTED_DISJUNCTIVE = TLAConstants.INDENT + TLAConstants.TLA_OR + TLAConstants.SPACE;
    
	private TLAConstants() { }
}
