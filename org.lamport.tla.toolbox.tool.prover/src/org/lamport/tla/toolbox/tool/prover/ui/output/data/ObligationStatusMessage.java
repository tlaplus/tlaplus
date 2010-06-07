package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;

import tla2sany.st.Location;

/**
 * Contains data about the status of an obligation.
 * 
 * @author drickett
 *
 */
public class ObligationStatusMessage extends TLAPMMessage
{

    public static final String ID_FIELD = "id";
    public static final String METH_FIELD = "meth";
    public static final String OBL_FIELD = "obl";

    /**
     * Constant for verified status.
     */
    public static final int STATUS_VERIFIED = 0;
    /**
     * Constant for rejected status.
     */
    public static final int STATUS_REJECTED = 1;
    /**
     * Constant for unknown status.
     */
    public static final int STATUS_UNKNOWN = -1;

    /**
     * Status of the obligation.
     */
    private String status;
    /**
     * Location in module of obligation.
     */
    private Location location;
    /**
     * The obligation as a string.
     */
    private String obString;
    /**
     * The method used.
     */
    private String method;
    /**
     * The id of the obligation.
     */
    private int id;

    /**
     * 
     * @param offset
     * @param length
     * @param type
     * @param status see status constants in this class.
     */
    private ObligationStatusMessage()
    {
    }

    public String getStatus()
    {
        return status;
    }

    public Location getLocation()
    {
        return location;
    }

    public String getObString()
    {
        return obString;
    }

    public int getID()
    {
        return id;
    }

    public String getMethod()
    {
        return method;
    }

    /**
     * Creates a new {@link ObligationStatusMessage} from the {@link Set}
     * of {@link Entry} where the key of each {@link Entry} is the field
     * name and the value is the field value string as output by the TLAPM.
     * 
     * @param fieldPairs
     * @return
     */
    public static ObligationStatusMessage getObMessage(Set fieldPairs, String moduleName)
    {
        ObligationStatusMessage message = new ObligationStatusMessage();

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
                } else if (fieldName.equals(OBL_FIELD))
                {
                    message.obString = fieldValue;
                } else if (fieldName.equals(STATUS_FIELD))
                {
                    message.status = fieldValue;
                } else if (fieldName.equals(ID_FIELD))
                {
                    try
                    {
                        message.id = Integer.parseInt(fieldValue.trim());
                    } catch (NumberFormatException e)
                    {
                        ProverUIActivator.logError("Error parsing obligation id from TLAPM message. ID string : "
                                + fieldValue, e);
                    }
                } else if (fieldName.equals(METH_FIELD))
                {
                    message.method = fieldValue;
                } else
                {
                    ProverUIActivator.logDebug("Unknown field name : " + fieldName + ".");
                }
            }
        }

        return message;
    }

    public String toString()
    {
        return "---------Obligation status message--------" + "\nLOCATION : " + location + "\nID : " + id
                + "\nOBLIGATION : " + obString + "\nSTATUS : " + status + "\nMETHOD : " + method;
    }
}
