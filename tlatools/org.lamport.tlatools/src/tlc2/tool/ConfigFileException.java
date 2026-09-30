package tlc2.tool;

import tlc2.output.MP;
import util.Assert.TLCRuntimeException;

/**
 * Exceptions signaling errors in the config file
 * <br><b>Note:</b>This class is used instead of Assert.fail inside of the ModelConfig.
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ConfigFileException extends TLCRuntimeException
{
    public ConfigFileException(int errorCode, String[] parameters)
    {
        super(errorCode, parameters, MP.getMessage(errorCode, parameters));
    }

    public ConfigFileException(int errorCode, String[] parameters, Exception cause)
    {
        super(errorCode, MP.getMessage(errorCode, parameters), cause);
        this.parameters = parameters;
    }
}
