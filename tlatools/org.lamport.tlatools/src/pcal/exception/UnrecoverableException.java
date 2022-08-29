package pcal.exception;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class UnrecoverableException extends Throwable {
    /**
     *
     */
    private static final long serialVersionUID = 5651132038554471989L;

    public UnrecoverableException(final String message) {
        super(message);
    }
}
