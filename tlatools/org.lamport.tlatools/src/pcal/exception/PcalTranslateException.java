package pcal.exception;

import pcal.AST;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class PcalTranslateException extends UnrecoverablePositionedException {

    /**
     *
     */
    private static final long serialVersionUID = -5401952653536650870L;

    /**
     *
     */
    public PcalTranslateException(final String message, final AST elementAt2) {
        super(message, elementAt2);
    }

    /**
     *
     */
    public PcalTranslateException(final String message) {
        super(message);
    }

}
