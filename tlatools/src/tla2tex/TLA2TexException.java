package tla2tex;

/**
 * 
 * @author Daniel Ricketts
 * @version $Id$
 */
public class TLA2TexException extends RuntimeException
{

    private String error_message;

    /**
     * 
     */
    private static final long serialVersionUID = 6158929578245645265L;

    public TLA2TexException(String message)
    {
        error_message = message;
    }

    public String getMessage()
    {
        return error_message;
    }
}
