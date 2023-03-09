package tlc2.tool.liveness;

import tlc2.value.impl.CounterExample;

public class LiveCounterExampleException extends LiveException {

	public final CounterExample counterExample;

	public LiveCounterExampleException(int errorCode, String msg, CounterExample c) {
		super(errorCode, msg);
		this.counterExample = c;
	}
}
