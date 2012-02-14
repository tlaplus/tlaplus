package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;

/**
 * Represents a message from TLAPM that has one field, "count"
 * containing the number of obligations to be checked or proved.
 * 
 * @author Daniel Ricketts
 *
 */
public class ObligationNumberMessage extends TLAPMMessage
{
    /**
     * Number of obligations in the message.
     */
    private int count;

    /**
     * Field giving the number of obligations in the message.
     */
    public static final String COUNT_FIELD = "count";

    public static ObligationNumberMessage getObNumMessage(Set fieldPairs, String moduleName)
    {
        ObligationNumberMessage message = new ObligationNumberMessage();

        for (Iterator it = fieldPairs.iterator(); it.hasNext();)
        {
            Map.Entry nextEntry = (Map.Entry) it.next();
            String fieldName = (String) nextEntry.getKey();
            String fieldValue = (String) nextEntry.getValue();
            if (fieldName != null && fieldValue != null)
            {
                if (fieldName.equals(COUNT_FIELD))
                {
                    try
                    {
                        message.count = Integer.parseInt(fieldValue);
                    } catch (NumberFormatException e)
                    {
                        ProverUIActivator.getDefault().logError("Count field in message cannot be parsed to an int."
                                + "The message contains the fields " + fieldPairs, e);
                    }
                }
            }
        }

        return message;
    }

    /**
     * Returns the number of obligations in the message.
     * This is the number of obligations to be proved or checked.
     * 
     * @return the count
     */
    public int getCount()
    {
        return count;
    }

}
