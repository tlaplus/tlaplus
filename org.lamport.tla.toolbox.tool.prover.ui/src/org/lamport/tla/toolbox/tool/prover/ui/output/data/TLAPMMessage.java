package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.runtime.Assert;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.output.TagBasedTLAPMOutputIncrementalParser2;

import tla2sany.st.Location;
import util.UniqueString;

/**
 * Class for the data in a message of output
 * of the TLAPM.
 * 
 * A message of output consists of field name-value
 * pairs. This class has a method for every field
 * for retrieving an object representing the value
 * of that field. Since every message does not contain
 * every field, some of those methods can return null
 * for some types of messages.
 * 
 * In order to determine the type of a message, call
 * {@link TLAPMMessage#getMessageType()}.
 * 
 * @author Daniel Ricketts
 *
 */
public class TLAPMMessage
{
    public static final String TYPE_FIELD = "type";
    public static final String LOC_FIELD = "loc";
    public static final String STATUS_FIELD = "status";
    public static final String OBL_FIELD = "obl";

    public static final Pattern FIELD_PATTERN = Pattern.compile(TagBasedTLAPMOutputIncrementalParser2.DELIM + ":(\\w*)"/*<-1: the field name group*/
            + ":(.*)"/*<-2: the field value group*/);

    public static final String OB_STATUS_TYPE = "oblstatus";
    public static final String LEAF_STATUS_TYPE = "leafStatus";

    private String type;
    private Location location;
    private String status;
    private String obligation;

    /**
     * Returns the message type. This is one of {@link TLAPMMessage#OB_STATUS_TYPE}, {@link TLAPMMessage#LEAF_STATUS_TYPE}.
     * @return
     */
    public String getMessageType()
    {
        return type;
    }

    /**
     * Returns the location associated with this message or null
     * if there is no location associated with it.
     * @return
     */
    public Location getLocation()
    {
        return location;
    }
    
    /**
     * Returns the status of this message or null if there
     * is no status associated with this message type. If the
     * returned value is not null, it is one of
     * @return
     */
    public String getStatus()
    {
        return status;
    }
    
    /**
     * Returns the obligation associated with this message
     * or null if there is none.
     * 
     * @return
     */
    public String getObligation()
    {
        return obligation;
    }

    /**
     * Returns a {@link TLAPMMessage} representing the information
     * contained in proverMessage. The String proverMessage
     * should be the String between the tags @!!BEGIN and @!!END.
     * It can include these tags.
     * 
     * This returns null if no data can be parsed from
     * proverMessage.
     * 
     * @param proverMessage
     * @return
     */
    public static TLAPMMessage parseMessage(String proverMessage, String moduleName)
    {
        /*
         * The String proverMessage should be of the form
         * 
         * @!!<field-name>:<field-value>
         * @!!<field-name>:<field-value>
         * .
         * .
         * .
         * 
         * Possible field names right now are "loc" (location),
         * "status", and "obl" (obligation). In the future, there
         * might be a message type field, but for now, it is not used.
         */

        /*
         * We use the Pattern class to find strings matching
         * field name-value pairs and extract the name and value
         * using regular expression capturing groups.
         */
        Matcher matcher = FIELD_PATTERN.matcher(proverMessage);

        TLAPMMessage message = new TLAPMMessage();

        // flag indicating if the type field has been found
        // in the message
        boolean typeFieldFound = false;

        while (matcher.find())
        {
            String fieldName = matcher.group(1);
            String fieldValue = matcher.group(2);
            if (fieldName != null && fieldValue != null)
            {
                if (fieldName.equals(TYPE_FIELD))
                {
                    typeFieldFound = true;
                    message.type = fieldValue;
                } else if (fieldName.equals(LOC_FIELD))
                {
                    try
                    {
                        /*
                         * Attempt to parse bl, bc, el, ec from
                         * the field value.
                         * 
                         * fieldValue should be of the form:
                         * 
                         * "bl:bc:el:ec"
                         * 
                         * For now, we pass in null as the module name.
                         * I don't think it needs to be stored in this
                         * class.
                         */
                        String[] coordinates = fieldValue.split(":");
                        Assert.isTrue(coordinates.length >= 4, "Not enough coordinates found in location string "
                                + fieldName);
                        message.location = new Location(UniqueString.uniqueStringOf(moduleName), Integer
                                .parseInt(coordinates[0]), Integer.parseInt(coordinates[1]), Integer
                                .parseInt(coordinates[2]), Integer.parseInt(coordinates[3]));
                    } catch (NumberFormatException e)
                    {
                        ProverUIActivator.logError("Error parsing location from TLAPM message. Location string : "
                                + fieldValue, e);
                    }
                } else if (fieldName.equals(OBL_FIELD))
                {
                    message.obligation = fieldValue;
                } else if (fieldName.equals(STATUS_FIELD))
                {
                    message.status = fieldValue;
                } else
                {
                    ProverUIActivator.logDebug("Unknown field name : " + fieldName + ".");
                }
            } else
            {
                ProverUIActivator.logDebug("Null field name or value when parsing message. This is a bug. Message:");
                ProverUIActivator.logDebug(proverMessage);
            }
        }

        if (typeFieldFound)
        {
            return message;
        } else
        {
            ProverUIActivator.logDebug("Type field not found in TLAPM message. The message follows.");
            ProverUIActivator.logDebug(proverMessage);
        }

        return null;
    }
}
