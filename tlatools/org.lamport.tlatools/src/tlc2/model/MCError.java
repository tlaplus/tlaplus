package tlc2.model;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.ValueVec;
import util.TLAConstants;

/**
 * Class encapsulating information about an error trace found by TLC model checking.
 */
public class MCError {
	
	/**
	 * Human-readable message describing cause of error trace.
	 */
	private final String message;
	
	/**
	 * Nested error. It is uncertain whether or how nested errors ever occur.
	 */
	private final MCError cause;
	
	/**
	 * Sequence of states which comprise the error trace.
	 */
	private final ArrayList<MCState> states;
	
	/**
	 * Initializes a new instance of the {@link MCError} class.
	 */
	public MCError() {
		this(null);
	}
	
	/**
	 * Initializes a new instance of the {@link MCError} class.
	 * @param errorMessage Message describing the error.
	 */
	public MCError(final String errorMessage) {
		this(null, errorMessage);
	}
	
	/**
	 * Initializes a new instance of the {@link MCError} class.
	 * @param errorCause A nested error.
	 * @param errorMessage Message describing the error.
	 */
	public MCError(final MCError errorCause, final String errorMessage) {
		this.cause = errorCause;
		this.message = errorMessage;
		this.states = new ArrayList<>();
	}
	
	/**
	 * Adds a state to the error trace.
	 * @param state The state to add to the trace.
	 */
	public void addState(final MCState state) {
		this.states.add(state);
	}
	
	/**
	 * Gets the ordered list of states in the error trace.
	 * @return An ordered list of states comprising the error trace.
	 */
	public List<MCState> getStates() {
		return this.states;
	}
	
	/**
	 * Gets the message describing the error.
	 * @return A message describing the error.
	 */
	public String getMessage() {
		return this.message;
	}
	
	/**
	 * Returns the nested error.
	 * @return The nested error. Likely to be null.
	 */
	public MCError getCause() {
		return this.cause;
	}
	
	public void updateStatesForTraceExpression(final Map<String, String> variableExpressionMap) {
		for (final MCState state : states) {
			for (final MCVariable variable : state.getVariables()) {
				final String expression = variableExpressionMap.get(variable.getName());

				if (expression != null) {
					variable.setTraceExpression(expression);
				}
			}
		}
	}

	public String toSequenceOfRecords(final boolean includeHeaders) {
		final StringBuilder buf = new StringBuilder();
		buf.append(TLAConstants.BEGIN_TUPLE);
		buf.append(TLAConstants.CR);
		
		for (int i = 0; i < states.size(); i++) {
			final MCState tlcState = states.get(i);
			
			if (tlcState.isBackToState() || tlcState.isStuttering()) {
				//TODO How to represent these two types of states?
				continue;
			}
			
			if ((tlcState.getVariables().length == 0) && !includeHeaders) {
				// When an user has used filtering to hide all variables, the error trace here
				// has no variables. In this case just return empty sequence <<>> by breaking
				// from the loop.
				break;
			}
			
			if (i > 0) {
				// Append a comma if a record is going to be added below.
				buf.append(TLAConstants.COMMA).append(TLAConstants.CR);
			}
			buf.append(tlcState.asRecord(includeHeaders));
		}
			
		buf.append(TLAConstants.CR);
		buf.append(TLAConstants.END_TUPLE);
		return buf.toString();
	}

	public boolean isLasso() {
		if (this.states.isEmpty()) {
			return false;
		}
		return this.states.get(this.states.size() - 1).isBackToState();
	}
	
	/**
	 * The same state or states may appear multiple times in a (liveness) trace. For
	 * example, a trace could be s -> t -> s -> u with u closing the lasso back to
	 * the *first* s. (trace violates e.g. a property s.t. <>[]t \/ <>[]u. In other
	 * words, t and u are mutually exclusive).
	 */
	public boolean isLassoWithDuplicates() {
		if (isLasso()) {
			final ValueVec valueVec = new ValueVec();
			for (int i = 0; i < states.size() - 1; i++) {
				valueVec.addElement(states.get(i).getRecord());
			}
			return this.states.size() != new SetEnumValue(valueVec, false).size();
		}
		return false;
	}
}
