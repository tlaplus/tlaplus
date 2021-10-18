package tlc2.tool;

@SuppressWarnings("serial")
public class StatefulRuntimeException extends RuntimeException {

	private boolean isKnown = false;
	
	public StatefulRuntimeException() {
		super();
	}

	public StatefulRuntimeException(String message) {
		super(message);
	}

	public StatefulRuntimeException(String message, Throwable cause) {
		super(message, cause);
	}

	public boolean setKnown() {
		boolean old = isKnown;
		isKnown = true;
		return old;
	}

	public boolean isKnown() {
		return isKnown;
	}
}
