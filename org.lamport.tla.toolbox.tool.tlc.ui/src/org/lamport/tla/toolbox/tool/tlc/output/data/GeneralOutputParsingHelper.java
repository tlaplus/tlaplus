package org.lamport.tla.toolbox.tool.tlc.output.data;

import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

/**
 * A set of parsing methods 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class GeneralOutputParsingHelper
{

    public final static String OB = "(";
    public final static String CB = ")";

    /**
     * Parses the TLC start/finish time
     * @param message
     * @return
     */
    public static String parseTLCTimestamp(String message)
    {
        // handle errors
        if (message.indexOf(OB) != -1 && message.indexOf(CB) != -1)
        {
            return message.substring(message.indexOf(OB) + 1, message.indexOf(CB));
        } else
        {
            TLCUIActivator.logDebug("Error parsing TLC Timestamp.");
            return "";
        }
    }
}
