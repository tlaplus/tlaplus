package util;

/**
 * This exception is signaling that the caller (the developer) is using a wrong invocation.
 * Especially it is written in cases in which some non-implemented implementation is invoked or
 * implementation is used not as expected.
 * @author Simon Zambrovski
 * @version $Id$
 */
public class WrongInvocationException extends RuntimeException
{

    public WrongInvocationException(String message)
    {
        super(message);
    }

}
