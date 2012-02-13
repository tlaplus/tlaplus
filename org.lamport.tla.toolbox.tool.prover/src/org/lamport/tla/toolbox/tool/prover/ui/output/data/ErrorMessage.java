package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;

/**
 * Class representing an error message sent by tlapm. Such messages
 * are sent if there is buggy behavior in tlapm. The message typically
 * contains some information to be reported to tlapm developers.
 * 
 * @author Daniel Ricketts
 *
 */
public class ErrorMessage extends TLAPMMessage
{

    /**
     * The field name whose value is the warning message. 
     */
    public static final String MSG_FIELD = "msg";
    /**
     * The field name whose value is a url. This url
     * can be used to submit bug reports.
     */
    public static final String URL_FIELD = "url";

    /**
     * The error message.
     */
    private String message;
    /**
     * The url contained in the message.
     */
    private String url;

    /**
     * Creates a new {@link ErrorMessage} from the {@link Set}
     * of {@link Entry} where the key of each {@link Entry} is the field
     * name and the value is the field value string as output by the TLAPM.
     * 
     * This method expects a field {@link #MSG_FIELD} and a field {@link #URL_FIELD}.
     * 
     * @param fieldPairs
     * @param moduleName
     * @return
     */
    public static ErrorMessage getErrorMessage(Set fieldPairs, String moduleName)
    {

        ErrorMessage message = new ErrorMessage();

        for (Iterator it = fieldPairs.iterator(); it.hasNext();)
        {
            Map.Entry nextEntry = (Map.Entry) it.next();
            String fieldName = (String) nextEntry.getKey();
            String fieldValue = (String) nextEntry.getValue();
            if (fieldName != null && fieldValue != null)
            {
                if (fieldName.equals(MSG_FIELD))
                {
                    message.message = fieldValue;
                } else if (fieldName.equals(URL_FIELD))
                {
                    message.url = fieldValue;
                } else
                {
                    ProverUIActivator.getDefault().logDebug("Unknown field name for warning message : " + fieldName + ".");
                }
            }
        }

        return message;

    }

    /**
     * Returns the error message from the tlapm.
     * 
     * @return
     */
    public String getMessage()
    {
        return message;
    }

    /**
     * Returns the String url from the tlapm.
     * 
     * @return
     */
    public String getURL()
    {
        return url;
    }

}
