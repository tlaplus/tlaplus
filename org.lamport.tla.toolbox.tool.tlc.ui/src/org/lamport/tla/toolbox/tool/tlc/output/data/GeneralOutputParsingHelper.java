package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Date;

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
	private static final SimpleDateFormat sdf = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss");

    /**
     * Parses the TLC start/finish time
     * @param message
     * @return
     */
    public static long parseTLCTimestamp(String message)
    {
        // handle errors
        if (message.indexOf(OB) != -1 && message.indexOf(CB) != -1)
        {
            final String time = message.substring(message.indexOf(OB) + 1, message.indexOf(CB));
            try {
            	return sdf.parse(time).getTime();
            } catch(ParseException e) {
                TLCUIActivator.logDebug("Error parsing TLC Timestamp.");
                return new Date().getTime();
            }
        } else
        {
            TLCUIActivator.logDebug("Error parsing TLC Timestamp.");
            return new Date().getTime();
        }
    }
}
