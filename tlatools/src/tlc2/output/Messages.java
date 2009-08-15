package tlc2.output;

import java.util.MissingResourceException;
import java.util.ResourceBundle;

/**
 * Retrieves the TLC messages
 * @author Simon Zambrovski
 * @version $Id$
 */
public class Messages
{
    // full path to the message file
    private static final String BUNDLE_NAME = "tlc2.output.messages"; //$NON-NLS-1$

    private static final ResourceBundle RESOURCE_BUNDLE = ResourceBundle.getBundle(BUNDLE_NAME);

    private Messages()
    {
    }

    /**
     * Retrieves the string by key
     * @param key 
     * @return
     */
    public static String getString(String key)
    {
        try
        {
            return RESOURCE_BUNDLE.getString(key);
        } catch (MissingResourceException e)
        {
            return '!' + key + '!';
        }
    }
}
