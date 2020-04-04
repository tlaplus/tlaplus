package pcal.exception;

import pcal.AST;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class PcalTLAGenException extends UnrecoverablePositionedException
{

    /**
     * @param message
     */
    public PcalTLAGenException(String message)
    {
        super(message);
    }

    /**
     * @param message
     * @param elementAt2
     */
    public PcalTLAGenException(String message, AST elementAt2)
    {
        super(message, elementAt2);
    }
    
    

}
