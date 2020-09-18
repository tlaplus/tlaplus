package tlc2.output;

import java.util.List;
import java.util.Optional;

import tlc2.model.MCError;
import tlc2.model.MCState;
import tlc2.tool.TLCStateInfo;

/**
 * Saves all messages containing info about error traces that pass through {@link tlc.output.MP}.
 * Ideally this will eventually go away and all of TLC's model checking implementations will
 * bubble their error traces up through their top-level .run() methods, but until that
 * refactoring takes place this is how we get the error trace: by hooking into the static
 * console output handler class and intercepting TLC output.
 * 
 * There are a number of places that error traces are generated within TLC:
 *  - Basic local BFS model checking in {@link tlc2.tool.ModelChecker#doNextCheckInvariants}
 *    > note: appears to be dead, the concurrent BFS implementation is always used instead
 *  - Concurrent local BFS model checking in {@link tlc2.tool.Worker#doNextCheckInvariants}
 *  - DFID local model checking in {@link tlc2.tool.DFIDModelChecker#doNext}
 *  - Simulator local model checking in {@link tlc2.tool.Simulator#simulate}
 *  - Liveness checking in {@link tlc2.tool.liveness.LiveCheck#check0}
 *  - Distributed model checking in {@link tlc2.tool.distributed.TLCServerThread#run}
 * All of these pass through {@link tlc2.output.StatePrinter} then {@link tlc.output.MP}.
 *  
 * The purpose of this class is to record error trace output from all of those sources while
 * ignoring output that is not an error trace (some of which superficially resembles error
 * traces, for example printing out an invalid/incomplete state transition).
 */
public class ErrorTraceMessagePrinterRecorder implements IMessagePrinterRecorder {
	
	/**
	 * The error trace, if one exists.
	 */
	private Optional<MCError> errorTrace = Optional.empty();
	
	/**
	 * Whether the trace has terminated or more states are expected;
	 */
	private boolean traceFinished = false;
	
	/**
	 * Gets the error trace, if it exists.
	 * @return The error trace.
	 */
	public Optional<MCError> getMCErrorTrace() {
		return this.errorTrace;
	}
	
	@Override
	public void record(int code, Object... objects) {
		if (!traceFinished) {
			switch (code) {
				case EC.TLC_STATE_PRINT2:
					if (objects.length >= 2
						&& objects[0] instanceof TLCStateInfo
						&& objects[1] instanceof Integer) {
						TLCStateInfo stateInfo = (TLCStateInfo)objects[0];
						Integer stateOrdinal = (Integer)objects[1];
						stateInfo.stateNumber = stateOrdinal;

						// Idempotent transition from no trace to safety trace
						this.errorTrace = Optional.of(this.errorTrace.orElse(new MCError()));

						// Add state to trace
						MCState state = new MCState(stateInfo);
						this.errorTrace.ifPresent(trace -> trace.addState(state));
					}

					break;
				case EC.TLC_STATE_PRINT3:
					// Mark trace as ending in stuttering
					this.traceFinished = true;
					this.errorTrace.ifPresent(trace -> {
						List<MCState> states = trace.getStates();
						if (states.size() > 0) {
							MCState finalState = states.get(states.size() - 1);
							MCState stutteringState = new MCState(finalState, true, false);
							trace.addState(stutteringState);
						}
					});

					break;
				case EC.TLC_BACK_TO_STATE:
					// Lasso reporting output varies based on -tool setting
					Optional<Integer> stateOrdinal = Optional.empty();
					if (objects.length >= 2
						&& objects[0] instanceof TLCStateInfo
						&& objects[1] instanceof Integer) {
						stateOrdinal = Optional.of((Integer)objects[1]);
					} else if (objects.length >= 2
						&& objects[0] instanceof String
						&& objects[1] instanceof String) {
						try {
							stateOrdinal = Optional.of(Integer.parseInt((String)objects[0]));
						} catch (NumberFormatException e) { }
					}

					stateOrdinal.ifPresent(ord -> {
						this.traceFinished = true;
						this.errorTrace.ifPresent(trace -> {
							List<MCState> states = trace.getStates();
							if (0 < ord && ord <= states.size()) {
								MCState finalState = states.get(ord - 1);
								MCState lassoState = new MCState(finalState, false, true);
								trace.addState(lassoState);
							}
						});
					});
					
					break;
			}
		}
	}
}
