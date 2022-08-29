package pcal.exception;

import pcal.AST;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class UnrecoverablePositionedException extends UnrecoverableException {
    /**
     *
     */
    private static final long serialVersionUID = 6824546728023633260L;
    private AST position;

    public UnrecoverablePositionedException(final String message) {
        super(message);
    }

    /**
     *
     */
    public UnrecoverablePositionedException(final String message, final AST position) {
        super(message);
        this.position = position;
    }

    /**
     * @return the elementAt
     */
    public AST getPosition() {
        return position;
    }

}
