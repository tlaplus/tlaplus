package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;

import tla2sany.st.Location;

/**
 * Contains data about the status of an obligation.
 * 
 * An obligation status message contains an id, method, status,
 * and potentially the pretty printed obligation string. These attributes
 * can be accessed by their respective get methods.
 * 
 * @author drickett
 *
 */
public class ObligationStatusMessage extends TLAPMMessage
{

    public static final String ID_FIELD = "id";
    public static final String METH_FIELD = "meth";
    public static final String OBL_FIELD = "obl";
    public static final String PROVER_FIELD = "prover";
    public static final String ALREADY_FIELD = "already";

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
     * The name of the backend used.
     */
    private String prover;
    /**
     * The method used by prover.
     */
    private String method;
    /**
     * The id of the obligation.
     */
    private int id;
    /**
     * True iff this status comes
     * from the fingerprints file.
     */
    private boolean alreadyProcessed = false;

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

    /**
     * Gets the string representing what the latest
     * status for this obligation is for the prover given
     * by {@link #getMethod()}.
     * 
     * @return
     */
    public String getStatus()
    {
        return status;
    }

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

    /**
     * Returns the pretty printed form of the obligation
     * if that is part of the message. Otherwise returns
     * null.
     * 
     * @return
     */
    public String getObString()
    {
        return obString;
    }

    /**
     * Returns the id of the obligation.
     * 
     * @return
     */
    public int getID()
    {
        return id;
    }

    /**
     * Returns the name of the backend for which this is
     * a message. tlapm, isabelle, zenon, etc.
     * 
     * Returns null if there is no prover associated
     * with this message. This occurs if the status
     * is {@link ProverHelper#TO_BE_PROVED}.
     * That is the first message that arrives for every
     * obligation.
     * 
     * @return
     */
    public String getBackend()
    {
        return prover;
    }

    /**
     * Returns the method used by the prover whose name is given
     * by {@link #getBackend()}. Cooper, auto, etc.
     * 
     * Returns null if there is no method associated
     * with this message. This currently only occurs
     * when the status is {@link ProverHelper#TO_BE_PROVED}
     * or {@link ProverHelper#TRIVIAL}.
     * 
     * @return
     */
    public String getMethod()
    {
        return method;
    }

    /**
     * Returns true iff this status comes
     * from the fingerprints file.
     */
    public boolean isAlreadyProcessed()
    {
        return alreadyProcessed;
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
                } else if (fieldName.equals(PROVER_FIELD))
                {
                    message.prover = fieldValue;
                } else if (fieldName.equals(ALREADY_FIELD))
                {
                    message.alreadyProcessed = Boolean.parseBoolean(fieldName.trim());
                } else
                {
                    ProverUIActivator.logDebug("Unknown field name for obligation status message : " + fieldName + ".");
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
