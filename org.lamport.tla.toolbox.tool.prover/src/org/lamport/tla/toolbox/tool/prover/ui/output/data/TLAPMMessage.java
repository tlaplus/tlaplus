package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.output.TagBasedTLAPMOutputIncrementalParser;

import tla2sany.st.Location;
import util.UniqueString;

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

    /**
     * Type of message containing information
     * on the status of an obligation.
     */
    public static final String OB_STATUS_TYPE = "obligation";
    /**
     * Type of message containing information on the
     * status of a proof step.
     */
    public static final String STEP_STATUS_TYPE = "proof-step";
    /**
     * Type of message containing information on the status
     * of a theorem.
     */
    public static final String THEOREM_STATUS_TYPE = "theorem";
    /**
     * Type of message containing the number of obligations
     * in the region being proved or checked.
     */
    public static final String OB_NUMBER_TYPE = "obligationsnumber";
    /**
     * Type of message containing some sort of warning message.
     */
    public static final String WARNING_TYPE = "warning";
    /**
     * Type of message containing some sort of error message.
     */
    public static final String ERROR_TYPE = "error";

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
        // System.out.println("New message to be parsed : \n" + proverMessage);
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
                        + fieldStrings[i] + "\n in message :" + proverMessage);

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
                return message;
            } else if (type.equals(STEP_STATUS_TYPE) || type.equals(THEOREM_STATUS_TYPE))
            {
                StepStatusMessage message = StepStatusMessage.getStepMessage(fieldPairs.entrySet(), moduleName);
                return message;
            } else if (type.equals(OB_NUMBER_TYPE))
            {
                ObligationNumberMessage message = ObligationNumberMessage.getObNumMessage(fieldPairs.entrySet(),
                        moduleName);
                return message;
            } else if (type.equals(WARNING_TYPE) || type.equals(ERROR_TYPE))
            {
                WarningMessage message = WarningMessage.getWarningMessage(fieldPairs.entrySet(), moduleName);
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

        /*
         * This first bad implementations of this method.
         */
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

    /**
     * Parses the location string returned by the prover
     * into an instance of {@link Location}. Null
     * if parsing is unsuccessful.
     * 
     * @param locString
     * @return
     */
    protected static Location parseLocation(String locString, String moduleName)
    {

        try
        {
            /*
             * Attempt to parse bl, bc, el, ec from
             * the locString.
             * 
             * locString should be of the form:
             * 
             * "bl:bc:el:ec"
             * 
             * For tlapm messages, ec corresponds to the
             * column after the last character in the location.
             * For example, if the location described the string
             * "ab", then bc would be n and ec would be n+2.
             * 
             * This is not consistent with SANY Locations, in which
             * the end column corresponds to the column before the last
             * character in the location. In the previous example, bc
             * would be n and ec would be n+1. We want the Locations to be
             * consistent in the Toolbox, so we subtract 1 from the ec
             * reported by the tlapm. 
             */
            String[] coordinates = locString.split(":");
            Assert.isTrue(coordinates.length >= 4, "Not enough coordinates found in location string : " + locString);
            return new Location(UniqueString.uniqueStringOf(moduleName), Integer.parseInt(coordinates[0]), Integer
                    .parseInt(coordinates[1]), Integer.parseInt(coordinates[2]), Integer.parseInt(coordinates[3]) - 1);
        } catch (NumberFormatException e)
        {
            ProverUIActivator.logError("Error parsing location from TLAPM message. Location string : " + locString, e);
        }
        return null;

    }
}
