package tlc2.model;

import java.util.ArrayList;
import java.util.List;

import util.TLAConstants;

public class MCError {
	private final String message;
	private final MCError cause;
	private final ArrayList<MCState> states;
	
	public MCError(final MCError errorCause, final String errorMessage) {
		cause = errorCause;
		message = errorMessage;
		states = new ArrayList<>();
	}
	
	public void addState(final MCState state) {
		states.add(state);
	}
	
	public List<MCState> getStates() {
		return states;
	}
	
	public String getMessage() {
		return message;
	}
	
	public MCError getCause() {
		return cause;
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
}
