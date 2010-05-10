package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.output.TagBasedTLAPMOutputIncrementalParser;

/**
 * Abstract class for the data in a message of output
 * of the TLAPM.
 * 
 * A message of output consists of field name-value
 * pairs. This class provides a common type to be extended
 * by all objects representing TLAPM messages.
 * 
 * It also contains a static method
 * {@link TLAPMMessage#parseMessage(String, String)} for parsing
 * a single message output by the TLAPM. It returns the appropriate
 * subtype of this class that represents the message.
 * 
 * @author Daniel Ricketts
 *
 */
public abstract class TLAPMMessage
{
    public static final String TYPE_FIELD = "type";
    public static final String LOC_FIELD = "loc";
    public static final String STATUS_FIELD = "status";

    /**
     * String that separates the field name from
     * its values, as in
     * 
     * <field-name>:<field-value>
     */
    public static final String FIELD_PAIR_SPLIT = ":";

    // public static final Pattern FIELD_PATTERN = Pattern.compile(TagBasedTLAPMOutputIncrementalParser2.DELIM +
    // "(\\w*)"/*<-1: the field name group*/
    // + ":(.*)"/*<-2: the field value group*/+ TagBasedTLAPMOutputIncrementalParser2.DELIM, Pattern.DOTALL);

    public static final String OB_STATUS_TYPE = "obligation";
    public static final String LEAF_STATUS_TYPE = "leafStatus";

    // private String type;
    // private Location location;
    // private String status;
    // private String obligation;

    // /**
    // * Returns the message type. This is one of {@link TLAPMMessage#OB_STATUS_TYPE}, {@link
    // TLAPMMessage#LEAF_STATUS_TYPE}.
    // * @return
    // */
    // public String getMessageType()
    // {
    // return type;
    // }

    // /**
    // * Returns the location associated with this message or null
    // * if there is no location associated with it.
    // * @return
    // */
    // public Location getLocation()
    // {
    // return location;
    // }

    // /**
    // * Returns the status of this message or null if there
    // * is no status associated with this message type. If the
    // * returned value is not null, it is one of
    // * @return
    // */
    // public String getStatus()
    // {
    // return status;
    // }

    // /**
    // * Returns the obligation associated with this message
    // * or null if there is none.
    // *
    // * @return
    // */
    // public String getObligation()
    // {
    // return obligation;
    // }

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
        System.out.println("New message to be parsed : \n" + proverMessage);
        /*
         * The String proverMessage should be of the form
         * 
         * @!!<field-name>:<field-value>
         * @!!<field-name>:<field-value>
         * .
         * .
         * .
         * 
         * One of the field names should be "type".
         * 
         * This method parses the type of the message,
         * then delegates the remaining parsing to the
         * subclass of TLAPM message that corresponds
         * to this type. It delegates this parsing
         * by passing a set of field-name,field-value
         * pairs to a static method of the subclass.
         */

        /*
         * First, we get all field-name, field-value pairs.
         * 
         * We split the string around all occurrences
         * of the delimiter @!!. Trim all strings
         * in between the delimiter and try to parse
         * field names and values.
         */
        String[] fieldStrings = proverMessage.split(TagBasedTLAPMOutputIncrementalParser.DELIM);

        String type = null;

        Map fieldPairs = new HashMap();

        for (int i = 0; i < fieldStrings.length; i++)
        {
            /*
             * The first element of the array may be the empty string.
             */
            if (!fieldStrings[i].trim().isEmpty())
            {
                /*
                 * The trimmed field string should be of the form
                 * <field-name>:<field-value>
                 * 
                 * Split the field string around the first
                 * occurrence of ":".
                 */
                String[] nameValPair = fieldStrings[i].trim().split(FIELD_PAIR_SPLIT, 2);
                Assert.isTrue(nameValPair.length == 2, "Encountered a flawed field name-value string : "
                        + fieldStrings[i]);

                String fieldName = nameValPair[0];
                String fieldValue = nameValPair[1];
                if (fieldName != null && fieldValue != null)
                {
                    if (fieldName.equals(TYPE_FIELD))
                    {
                        type = fieldValue;
                    } else
                    {
                        /*
                         * Put all name,value pairs that
                         * are not the message type into the map.
                         */
                        fieldPairs.put(fieldName, fieldValue);
                    }
                } else
                {
                    ProverUIActivator
                            .logDebug("Null field name or value when parsing message. This is a bug. Message:");
                    ProverUIActivator.logDebug(proverMessage);
                }
            }
        }

        if (type != null)
        {
            /*
             * Delegate the remaining parsing to the appropriate
             * subclass.
             */
            if (type.equals(OB_STATUS_TYPE))
            {
                ObligationStatusMessage message = ObligationStatusMessage.getObMessage(fieldPairs.entrySet(),
                        moduleName);
                System.out.println(message);
                return message;
            } else
            {
                ProverUIActivator.logDebug("Unsuppported message type " + type);
            }
        } else
        {
            ProverUIActivator.logDebug("Type field not found in TLAPM message. The message follows.");
            ProverUIActivator.logDebug(proverMessage);
        }
        return null;

        // TLAPMMessage message = new TLAPMMessage();
        //
        // /*
        // * We split the string around all occurrences
        // * of the delimiter @!!. Trim all strings
        // * in between the delimiter and try to parse
        // * field names and values.
        // */
        // String[] fieldStrings = proverMessage.split(TagBasedTLAPMOutputIncrementalParser2.DELIM);
        //
        // // flag indicating if the type field has been found
        // // in the message
        // boolean typeFieldFound = false;
        //
        // String type = null;
        //
        // Map fieldPairs = new HashMap();
        //
        // for (int i = 0; i < fieldStrings.length; i++)
        // {
        // /*
        // * The first element of the array may be the empty string.
        // */
        // if (!fieldStrings[i].trim().isEmpty())
        // {
        // /*
        // * The trimmed field string should be of the form
        // * <field-name>:<field-value>
        // *
        // * Split the field string around the first
        // * occurrence of ":".
        // */
        // String[] nameValPair = fieldStrings[i].trim().split(FIELD_PAIR_SPLIT, 2);
        // Assert.isTrue(nameValPair.length == 2, "Encountered a flawed field name-value string : "
        // + fieldStrings[i]);
        //
        // String fieldName = nameValPair[0];
        // String fieldValue = nameValPair[1];
        // if (fieldName != null && fieldValue != null)
        // {
        // fieldPairs.put(fieldName, fieldValue);
        // if (fieldName.equals(TYPE_FIELD))
        // {
        // typeFieldFound = true;
        // message.type = fieldValue;
        // type = fieldValue;
        // } else if (fieldName.equals(LOC_FIELD))
        // {
        // try
        // {
        // /*
        // * Attempt to parse bl, bc, el, ec from
        // * the field value.
        // *
        // * fieldValue should be of the form:
        // *
        // * "bl:bc:el:ec"
        // *
        // */
        // String[] coordinates = fieldValue.split(":");
        // Assert.isTrue(coordinates.length >= 4, "Not enough coordinates found in location string "
        // + fieldName);
        // message.location = new Location(UniqueString.uniqueStringOf(moduleName), Integer
        // .parseInt(coordinates[0]), Integer.parseInt(coordinates[1]), Integer
        // .parseInt(coordinates[2]), Integer.parseInt(coordinates[3]));
        // } catch (NumberFormatException e)
        // {
        // ProverUIActivator.logError("Error parsing location from TLAPM message. Location string : "
        // + fieldValue, e);
        // }
        // } else if (fieldName.equals(OBL_FIELD))
        // {
        // message.obligation = fieldValue;
        // } else if (fieldName.equals(STATUS_FIELD))
        // {
        // message.status = fieldValue;
        // } else
        // {
        // ProverUIActivator.logDebug("Unknown field name : " + fieldName + ".");
        // }
        // } else
        // {
        // ProverUIActivator
        // .logDebug("Null field name or value when parsing message. This is a bug. Message:");
        // ProverUIActivator.logDebug(proverMessage);
        // }
        // }
        // }
        //
        // if (typeFieldFound)
        // {
        // System.out.println("New message parsed : ");
        // System.out.println(message.toString());
        // return message;
        // } else
        // {
        // ProverUIActivator.logDebug("Type field not found in TLAPM message. The message follows.");
        // ProverUIActivator.logDebug(proverMessage);
        // }
        //
        // return null;

        // // flag indicating if the type field has been found
        // // in the message
        // boolean typeFieldFound = false;
        //
        // while (matcher.find())
        // {
        // String fieldName = matcher.group(1);
        // String fieldValue = matcher.group(2);
        // if (fieldName != null && fieldValue != null)
        // {
        // if (fieldName.equals(TYPE_FIELD))
        // {
        // typeFieldFound = true;
        // message.type = fieldValue;
        // } else if (fieldName.equals(LOC_FIELD))
        // {
        // try
        // {
        // /*
        // * Attempt to parse bl, bc, el, ec from
        // * the field value.
        // *
        // * fieldValue should be of the form:
        // *
        // * "bl:bc:el:ec"
        // *
        // */
        // String[] coordinates = fieldValue.split(":");
        // Assert.isTrue(coordinates.length >= 4, "Not enough coordinates found in location string "
        // + fieldName);
        // message.location = new Location(UniqueString.uniqueStringOf(moduleName), Integer
        // .parseInt(coordinates[0]), Integer.parseInt(coordinates[1]), Integer
        // .parseInt(coordinates[2]), Integer.parseInt(coordinates[3]));
        // } catch (NumberFormatException e)
        // {
        // ProverUIActivator.logError("Error parsing location from TLAPM message. Location string : "
        // + fieldValue, e);
        // }
        // } else if (fieldName.equals(OBL_FIELD))
        // {
        // message.obligation = fieldValue;
        // } else if (fieldName.equals(STATUS_FIELD))
        // {
        // message.status = fieldValue;
        // } else
        // {
        // ProverUIActivator.logDebug("Unknown field name : " + fieldName + ".");
        // }
        // } else
        // {
        // ProverUIActivator.logDebug("Null field name or value when parsing message. This is a bug. Message:");
        // ProverUIActivator.logDebug(proverMessage);
        // }
        //
        // matcher.region(matcher.end() - TagBasedTLAPMOutputIncrementalParser2.DELIM.length(), matcher.regionEnd());
        // }
        //
        // if (typeFieldFound)
        // {
        // System.out.println("New message parsed : ");
        // System.out.println(message.toString());
        // return message;
        // } else
        // {
        // ProverUIActivator.logDebug("Type field not found in TLAPM message. The message follows.");
        // ProverUIActivator.logDebug(proverMessage);
        // }
        //
        // return null;
    }

    // public String toString()
    // {
    // return "TYPE : " + type + "\nLOCATION : " + location + "\nSTATUS : " + status + "\nOBLIGATION : " + obligation;
    // }
}
