package pcal.exception;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class StringVectorToFileException extends UnrecoverableException
{

    /**
     * @param string
     */
    public StringVectorToFileException(String string)
    {
        super(string);
    }

}
