package org.lamport.tla.toolbox.tool.tlc.output.data;

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
        // TODO handle errors
        return message.substring(message.indexOf(OB) + 1, message.indexOf(CB));
    }
}
