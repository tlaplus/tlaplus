package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import java.util.Set;
import java.util.Map.Entry;

import tla2sany.st.Location;

public class StepStatusMessage extends TLAPMMessage
{

    public Location getLocation()
    {
        // TODO Auto-generated method stub
        return null;
    }

    public String getStatus()
    {
        // TODO Auto-generated method stub
        return null;
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

        return message;
    }

}
