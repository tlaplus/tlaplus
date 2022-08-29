package pcal.exception;

import pcal.AST;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParseAlgorithmException extends UnrecoverablePositionedException {

    /**
     *
     */
    private static final long serialVersionUID = 3784651974781713851L;

    /**
     *
     */
    public ParseAlgorithmException(final String message) {
        super(message);
    }

    /**
     *
     */
    public ParseAlgorithmException(final String message, final AST elementAt) {
        super(message, elementAt);
    }
}
