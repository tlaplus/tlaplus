package util;

/**
 * This exception is signaling that the caller (the developer) is using a wrong invocation.
 * Especially it is written in cases in which some non-implemented implementation is invoked or
 * implementation is used not as expected.
 *
 * @author Simon Zambrovski
 * @version $Id$
 */
public class WrongInvocationException extends RuntimeException {

    /**
     *
     */
    private static final long serialVersionUID = 3746913549917545561L;

    public WrongInvocationException(final String message) {
        super(message);
    }

}
