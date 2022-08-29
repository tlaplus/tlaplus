package pcal.exception;

import pcal.AST;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class PcalTLAGenException extends UnrecoverablePositionedException {

    /**
     *
     */
    private static final long serialVersionUID = -3722678227263123382L;

    /**
     *
     */
    public PcalTLAGenException(final String message) {
        super(message);
    }

    /**
     *
     */
    public PcalTLAGenException(final String message, final AST elementAt2) {
        super(message, elementAt2);
    }


}
