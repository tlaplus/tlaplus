package tlc2.model;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import tla2sany.st.Location;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.value.IValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.Value;
import util.TLAConstants;
import util.UniqueString;

/**
 * Encapsulates information about a TLC state.
 */
public class MCState {
	
	private static final String BACK_TO_STATE = " " + TLAConstants.BACK_TO_STATE;
	
	/**
	 * The variables captured by this state.
	 */
	private final MCVariable[] variables;
	
	/**
	 * The name of the next-state-relation taken to arrive in this state.
	 */
	private final String name;
	
	/**
	 * The state label; takes form of <$name $location>
	 */
	private final String label;
	
	/**
	 * The location of the next-state-relation, a parsed representation of (for example):
	 * line 7, col 9 to line 11, col 23 of module Alias
	 */
	private final Location location;
	
	/**
	 * Whether this state was reached by stuttering.
	 * Found in behaviors witnessing a liveness property violation.
	 */
	private final boolean isStuttering;
	
	/**
	 * Whether this state returns to a previous state in the behavior.
	 * Found in behaviors witnessing a liveness property violation.
	 */
	private final boolean isBackToState;
	
	/**
	 * The depth of this state in the behavior, counting from 1.
	 */
	private final int stateNumber;

	private RecordValue record;

	/**
	 * Parses a state from the standard TLC command line output format, for example:
	 * 
	 * 3: <Next line 7, col 9 to line 11, col 23 of module Alias>
	 * /\ x = 3
	 * /\ y = FALSE
	 * 
	 * @param stateInputString The unparsed state in TLC command line output format.
	 * @return A parsed {@link MCState} instance.
	 */
	public static MCState parseState(final String stateInputString) {
		// state number
		final int index = stateInputString.indexOf(TLAConstants.COLON);
		// multi line
		int index2 = stateInputString.indexOf(TLAConstants.CR, index);
		if (index2 == -1) {
			index2 = stateInputString.length();
		}

		final int stateNumber = Integer.parseInt(stateInputString.substring(0, index).trim());
		final String label = stateInputString.substring((index + 1), index2);
		final boolean isStuttering = (label.indexOf(TLAConstants.STUTTERING) == 0);
		final boolean isBackToState = (label.indexOf(BACK_TO_STATE) == 0);

		MCVariable[] vars = null;
		final String name;
		final Location location;
		if (!isBackToState && !isStuttering) {
			// string from which the variables can be parsed
			final String variableInputString = stateInputString.substring(index2 + 1);
			vars = parseVariables(variableInputString);
			
			// The format of states in the output of depth-first (iterative deepening)
			// obviously differs from BFS (why use one implementation when we can have 2 and
			// more). Thus, take care of states that lack a label.
			final String sublabel;
			if (label.length() > 2) {
				sublabel = label.substring(2, (label.length() - 1));

				final int lineIndex = sublabel.indexOf(TLAConstants.LINE);
				if (lineIndex != -1) {
					name = sublabel.substring(0, (lineIndex - 1));
					location = Location.parseLocation(sublabel.substring(lineIndex));
				} else {
					name = sublabel;
					location = null;
				}
			} else {
				name = null;
				location = null;
			}
		} else {
			name = null;
			location = null;
		}

		return new MCState(vars, name, label, location, isStuttering, isBackToState, stateNumber);
	}
	
	/**
	 * @param vars            variables in this state.
	 * @param stateName       the name for this state
	 * @param stateLabel      the display label, usually including line location and module
	 * @param moduleLocation  the name of this module whose checking this state is from
	 * @param stuttering      whether this is a stuttering state or not
	 * @param backToState     whether this is a back to state or not
	 * @param ordinal         number of the state in the trace
	 */
	public MCState(
			final MCVariable[] vars,
			final String stateName,
			final String stateLabel,
			final Location moduleLocation,
			final boolean stuttering,
			final boolean backToState,
			final int ordinal) {
		variables = vars;
		name = stateName;
		label = stateLabel;
		location = moduleLocation;
		isStuttering = stuttering;
		isBackToState = backToState;
		stateNumber = ordinal;
	}
	
	/**
	 * Initializes a new instance of this class.
	 * @param other The state from which to copy values.
	 * @param isStuttering Whether to mark this state as stuttering.
	 * @param isBackToState Whether to mark this state as the end of a lasso.
	 */
	public MCState(final MCState other, boolean isStuttering, boolean isBackToState) {
		this.variables = other.variables;
		this.name = other.name;
		this.label = other.label;
		this.location = other.location;
		this.stateNumber = other.stateNumber;
		this.isStuttering = isStuttering;
		this.isBackToState = isBackToState;
	}
	
	public MCState(TLCStateInfo tlcState) {
		this.name = "";
		this.label = "";
		this.location = null;
		this.isStuttering = false;
		this.isBackToState = false;
		this.stateNumber = (int)tlcState.stateNumber;

		Map<UniqueString, IValue> variableMap = tlcState.getOriginalState().getVals();
		List<MCVariable> variableList = new ArrayList<MCVariable>();
		for (UniqueString key : variableMap.keySet()) {
			IValue value = variableMap.get(key);
			// value is null if the successor state is not completely specified by the
			// next-state relation. See e.g. IncompleteNextTest.java
			MCVariable variable = new MCVariable(key.toString(), value);
			variableList.add(variable);
		}
		
		this.variables = variableList.toArray(new MCVariable[variableList.size()]);
		this.record = new RecordValue(tlcState.getOriginalState());
	}

	public MCVariable[] getVariables() {
		return this.variables;
	}
	
	public String getLabel() {
		 return this.label;
	}
	
	public String getName() {
		return this.name;
	}

	public boolean isStuttering() {
		return this.isStuttering;
	}

	public boolean isBackToState() {
		return this.isBackToState;
	}

	public int getStateNumber() {
		return this.stateNumber;
	}
	
	public Location getLocation() {
		return this.location;
	}
	
	public String asRecord(final boolean includeHeader) {
		final StringBuilder result = new StringBuilder();
		result.append(TLAConstants.L_SQUARE_BRACKET);
		result.append(TLAConstants.CR);
		
		if (includeHeader) {
			result.append(TLAConstants.SPACE);
			result.append(TLAConstants.TraceExplore.ACTION);
			result.append(TLAConstants.RECORD_ARROW);
			
			result.append(TLAConstants.L_SQUARE_BRACKET);
			result.append(TLAConstants.CR);
			result.append(TLAConstants.SPACE).append(TLAConstants.SPACE).append(TLAConstants.SPACE);
				result.append("position");
				result.append(TLAConstants.RECORD_ARROW);
				result.append(getStateNumber());
				result.append(TLAConstants.COMMA).append(TLAConstants.CR);
			
				result.append(TLAConstants.SPACE).append(TLAConstants.SPACE).append(TLAConstants.SPACE);
				result.append("name");
				result.append(TLAConstants.RECORD_ARROW);
				result.append(TLAConstants.QUOTE);
				result.append(name);
				result.append(TLAConstants.QUOTE);
				result.append(TLAConstants.COMMA).append(TLAConstants.CR);
				
				result.append(TLAConstants.SPACE).append(TLAConstants.SPACE).append(TLAConstants.SPACE);
				result.append("location");
				result.append(TLAConstants.RECORD_ARROW);
				result.append(TLAConstants.QUOTE);
				result.append(location);
				result.append(TLAConstants.QUOTE);
				
			result.append(TLAConstants.CR);
			result.append(TLAConstants.SPACE).append(TLAConstants.R_SQUARE_BRACKET);
			if (variables.length != 0) {
				// only append comma for additional records iff there are any variables to
				// append.
				result.append(TLAConstants.COMMA).append(TLAConstants.CR);
			}
		}
		
		for (int i = 0; i < variables.length; i++) {
			final MCVariable variable = variables[i];
			if (variable.isTraceExplorerExpression()) {
				result.append(variable.getSingleLineDisplayName());
			} else {
				result.append(variable.getName());
			}

			result.append(TLAConstants.RECORD_ARROW);

			result.append(variable.getValueAsString());
			
			if (i < (variables.length - 1)) {
				result.append(TLAConstants.COMMA).append(TLAConstants.CR);
			}
		}
		
		result.append(TLAConstants.CR).append(TLAConstants.R_SQUARE_BRACKET);
		return result.toString();
	}

	public String asSimpleRecord() {
		final StringBuilder buf = new StringBuilder();
		buf.append(TLAConstants.L_SQUARE_BRACKET);
		for (int i = 0; i < variables.length; i++) {
			final MCVariable var = variables[i];

			buf.append(var.getName());
			buf.append(TLAConstants.RECORD_ARROW);
			buf.append(var.getValueAsString());

			if (i < variables.length - 1) {
				buf.append(TLAConstants.COMMA);
			}
		}
		buf.append(TLAConstants.R_SQUARE_BRACKET);
		return buf.toString();
	}

    /**
     * The returns a conjunction list of variables.
     * 
     * For variables representing trace explorer expressions, if {@code includeTraceExpressions} is true,
     * the returned string has:
     * 
     * /\ expr = value
     * 
     * where expr is the single line form of the trace explorer expression as shown in the Name column of
     * the trace viewer.
     *  
     * For all other variables, this method attempts to display them as TLC does.
     * 
     * @param includeTraceExpressions whether trace expressions should be included.
     * @param indent if non-null, this will be prepended to each line
     * @return
     */
    public String getConjunctiveDescription(final boolean includeTraceExpressions, final String indent) {
        return getConjunctiveDescription(includeTraceExpressions, indent, false);
    }

    /**
     * The returns a conjunction list of variables.
     * 
     * For variables representing trace explorer expressions, if {@code includeTraceExpressions} is true,
     * the returned string has:
     * 
     * /\ expr = value
     * 
     * where expr is the single line form of the trace explorer expression as shown in the Name column of
     * the trace viewer.
     *  
     * For all other variables, this method attempts to display them as TLC does.
     * 
     * @param includeTraceExpressions whether trace expressions should be included.
     * @param indent if non-null, this will be prepended to each line
     * @param ansiMarkup if true, the String will include ANSI markup for trace expressions; this is currently ignored
     * 							if includeTraceExpressions is false
     * @return
     */
    public String getConjunctiveDescription(final boolean includeTraceExpressions, final String indent,
    										final boolean ansiMarkup) {
        final StringBuilder result = new StringBuilder();
        
		for (int i = 0; i < variables.length; i++) {
			final MCVariable var = variables[i];
			
			if (var.isTraceExplorerExpression() && !includeTraceExpressions) {
				continue;
			}
			
			if (indent != null) {
				result.append(indent);
			}
			
            result.append("/\\ ");
			if (var.isTraceExplorerExpression()) {
				if (ansiMarkup) {
					result.append(TLAConstants.ANSI.BOLD_CODE);
				}
				
				result.append(var.getSingleLineDisplayName());
			} else {
				result.append(var.getName());
			}

            result.append(" = ").append(var.getValueAsString());

			if (var.isTraceExplorerExpression() && ansiMarkup) {
				result.append(TLAConstants.ANSI.RESET_CODE);
			}
			
            result.append('\n');
        }
		
        return result.toString();
    }

	
	private static MCVariable[] parseVariables(final String variableInputString) {
		String[] lines = variableInputString.split(TLAConstants.CR);
		ArrayList<MCVariable> vars = new ArrayList<>();
		int index;

		// buffer for accumulating the state variable
		String[] stateVarString = null;

		// iterate line-wise
		for (int j = 0; j < lines.length; j++) {
			// find the index of the first /\ in the line
			index = lines[j].indexOf(TLAConstants.TLA_AND);
			// adding the current line to the previous lines
			if (index != -1) {
				// there was something in the buffer for the state variable
				// found an empty line, which means that this is the end of the current state
				if (stateVarString != null) {
					final MCVariable var = new MCVariable(stateVarString[0], stateVarString[1]);
					vars.add(var);
				}

				stateVarString = lines[j].substring(index + TLAConstants.TLA_AND.length() + 1).split(TLAConstants.EQ);
			} else {
				// no index

				if (stateVarString != null) {
					// either an empty line
					stateVarString[1] += TLAConstants.CR;
					stateVarString[1] += lines[j];
				} else {
					// the state has one variable only
					stateVarString = lines[j].split(TLAConstants.EQ);
				}
			}
		}

		// write the last one
		if (stateVarString != null) {
			final MCVariable var = new MCVariable(stateVarString[0], stateVarString[1]);
			vars.add(var);
		}

		return (MCVariable[]) vars.toArray(new MCVariable[vars.size()]);
	}

	public Value getRecord() {
		return record;
	}
}
