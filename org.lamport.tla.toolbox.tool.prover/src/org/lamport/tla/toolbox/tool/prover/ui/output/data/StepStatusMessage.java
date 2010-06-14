package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import tla2sany.st.Location;

/**
 * Contains data about the status of a proof step.
 * 
 * @author Daniel Ricketts
 *
 */
public class StepStatusMessage extends TLAPMMessage
{

    private Location location;
    private String status;

    /**
     * Returns the location describing the step.
     * This location is consistent with SANY Locations
     * in that the end column corresponds to the column before the last
     * character in the location.
     * For example, if the location described the string
     * "ab", then begin column would be n and end column would be n+1.
     * 
     * @return
     */
    public Location getLocation()
    {
        return location;
    }

    public String getStatus()
    {
        return status;
    }

    /**
     * Creates a new {@link ObligationStatusMessage} from the {@link Set}
     * of {@link Entry} where the key of each {@link Entry} is the field
     * name and the value is the field value string as output by the TLAPM.
     * 
     * @param fieldPairs
     * @return
     */
    public static StepStatusMessage getStepMessage(Set fieldPairs, String moduleName)
    {
        StepStatusMessage message = new StepStatusMessage();

        for (Iterator it = fieldPairs.iterator(); it.hasNext();)
        {
            Map.Entry nextEntry = (Map.Entry) it.next();
            String fieldName = (String) nextEntry.getKey();
            String fieldValue = (String) nextEntry.getValue();
            if (fieldName != null && fieldValue != null)
            {
                if (fieldName.equals(LOC_FIELD))
                {
                    message.location = parseLocation(fieldValue, moduleName);
                } else if (fieldName.equals(STATUS_FIELD))
                {
                    message.status = fieldValue;
                }
            }
        }

        return message;
    }

}
