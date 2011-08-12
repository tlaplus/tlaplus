package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;

/**
 * Class representing a warning message sent from the tlapm
 * to the Toolbox. For example, "bad fingerprints format - notloaded".
 * 
 * @author Daniel Ricketts
 *
 */
public class WarningMessage extends TLAPMMessage
{

    /**
     * The field name whose value is the warning message. 
     */
    public static final String MSG_FIELD = "msg";

    /**
     * The warning message.
     */
    private String message;

    /**
     * Creates a new {@link WarningMessage} from the {@link Set}
     * of {@link Entry} where the key of each {@link Entry} is the field
     * name and the value is the field value string as output by the TLAPM.
     * 
     * This method expects the only field to have the name "msg".
     * 
     * @param fieldPairs
     * @param moduleName
     * @return
     */
    public static WarningMessage getWarningMessage(Set fieldPairs, String moduleName)
    {

        WarningMessage message = new WarningMessage();

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
                } else
                {
                    ProverUIActivator.logDebug("Unknown field name for warning message : " + fieldName + ".");
                }
            }
        }

        return message;

    }

    /**
     * Returns the warning message from the tlapm.
     * 
     * @return
     */
    public String getMessage()
    {
        return message;
    }

}
