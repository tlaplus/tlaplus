package pcal.exception;

import pcal.AST;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParseAlgorithmException extends UnrecoverablePositionedException
{

    /**
     * @param message
     */
    public ParseAlgorithmException(String message)
    {
        super(message);
    }

    /**
     * @param string
     * @param elementAt
     */
    public ParseAlgorithmException(String message, AST elementAt)
    {
        super(message, elementAt);
    }
}
