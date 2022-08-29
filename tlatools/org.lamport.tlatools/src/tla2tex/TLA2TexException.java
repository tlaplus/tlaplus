package tla2tex;

/**
 * @author Daniel Ricketts
 * @version $Id$
 */
public class TLA2TexException extends RuntimeException {

    /**
     *
     */
    private static final long serialVersionUID = 6158929578245645265L;
    private final String error_message;

    public TLA2TexException(final String message) {
        error_message = message;
    }

    @Override
    public String getMessage() {
        return error_message;
    }
}
