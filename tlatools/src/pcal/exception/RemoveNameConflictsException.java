package pcal.exception;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class RemoveNameConflictsException extends UnrecoverablePositionedException
{

    /**
     * @param message
     */
    public RemoveNameConflictsException(String message)
    {
        super(message);
    }

    /**
     * @param e2
     */
    public RemoveNameConflictsException(UnrecoverablePositionedException e2)
    {
        super(e2.getMessage(), e2.getPosition());
    }

}
