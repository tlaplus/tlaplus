package pcal;

/**
 * Exception thrown instead of System.exit().
 * 
 * @author Simon Zambrovski
 * @version $Id$
 * @deprecated TODO this should be re-factored and not used further 
 */
public class PCalUnrecoverableErrorRuntimeException extends RuntimeException
{

    public PCalUnrecoverableErrorRuntimeException(String message)
    {
        super(message);
    }

}
