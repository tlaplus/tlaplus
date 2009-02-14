package pcal.exception;

import pcal.AST;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class UnrecoverablePositionedException extends UnrecoverableException
{
    private AST position;
    
    public UnrecoverablePositionedException(String message)
    {
        super(message);
    }

    /**
     * @param message
     * @param position
     */
    public UnrecoverablePositionedException(String message, AST position)
    {
        super(message);
        this.position = position;
    }
    
    /**
     * @return the elementAt
     */
    public AST getPosition()
    {
        return position;
    }

}
