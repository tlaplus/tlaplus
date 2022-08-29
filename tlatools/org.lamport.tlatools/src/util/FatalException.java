package util;

public class FatalException extends RuntimeException {
    private static final long serialVersionUID = -2030383158972968448L;
    public final int errorCode;

    public FatalException(String message, Throwable cause, int errorCode) {
        super(message, cause);
        this.errorCode = errorCode;
    }

    public FatalException(String message, Throwable cause) {
        this(message, cause, 1);
    }

    public FatalException(String message, int errorCode) {
        super(message);
        this.errorCode = errorCode;
    }

    public FatalException(String message) {
        this(message, 1);
    }
}
