package tlc2.tool;

@SuppressWarnings("serial")
public class StatefulRuntimeException extends RuntimeException {

    private boolean isKnown = false;

    public StatefulRuntimeException() {
        super();
    }

    public StatefulRuntimeException(final String message) {
        super(message);
    }

    public StatefulRuntimeException(final String message, final Throwable cause) {
        super(message, cause);
    }

    public boolean setKnown() {
        final boolean old = isKnown;
        isKnown = true;
        return old;
    }

    public boolean isKnown() {
        return isKnown;
    }
}
