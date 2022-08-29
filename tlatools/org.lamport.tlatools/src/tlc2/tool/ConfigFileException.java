package tlc2.tool;

import tlc2.output.MP;

/**
 * Exceptions signaling errors in the config file
 * <br><b>Note:</b>This class is used instead of Assert.fail inside of the ModelConfig.
 *
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ConfigFileException extends RuntimeException {
    /**
     *
     */
    private static final long serialVersionUID = 1479692626467317310L;

    public ConfigFileException(final int errorCode, final String[] parameters) {
        super(MP.getMessage(errorCode, parameters));
    }

    public ConfigFileException(final int errorCode, final String[] parameters, final Exception cause) {
        super(MP.getMessage(errorCode, parameters), cause);
    }
}
