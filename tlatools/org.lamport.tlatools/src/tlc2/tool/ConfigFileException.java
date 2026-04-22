package tlc2.tool;

import tlc2.output.MP;

/**
 * Exceptions signaling errors in the config file
 * <br><b>Note:</b>This class is used instead of Assert.fail inside of the ModelConfig.
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ConfigFileException extends RuntimeException
{
    /**
     * The error code for this exception, drawn from the error-code domain
     * defined in {@link tlc2.output.EC} (e.g. {@code EC.CFG_ERROR_READING_FILE}).
     */
    private final int errorCode;

    public ConfigFileException(int errorCode, String[] parameters)
    {
        super(MP.getMessage(errorCode, parameters));
        this.errorCode = errorCode;
    }

    public ConfigFileException(int errorCode, String[] parameters, Exception cause)
    {
        super(MP.getMessage(errorCode, parameters), cause);
        this.errorCode = errorCode;
    }

    /**
     * @return the error code for this exception, a constant from the
     * error-code domain defined in {@link tlc2.output.EC}.
     */
    public int getErrorCode()
    {
        return errorCode;
    }
}
