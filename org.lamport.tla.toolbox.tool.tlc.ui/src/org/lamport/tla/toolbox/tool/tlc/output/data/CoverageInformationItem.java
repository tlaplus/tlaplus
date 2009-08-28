package org.lamport.tla.toolbox.tool.tlc.output.data;

/**
 * Coverage information item
 * @author Simon Zambrovski
 * @version $Id$
 */
public class CoverageInformationItem
{
    private String module;
    private String location;
    private long count;

    /**
     * @param module2
     * @param location2
     * @param count2
     */
    public CoverageInformationItem(String module, String location, long count)
    {
        this.module = module;
        this.location = location;
        this.count = count;
    }

    public final String getModule()
    {
        return module;
    }

    public final String getLocation()
    {
        return location;
    }

    public final long getCount()
    {
        return count;
    }

    /**
     * @param outputMessage
     * @return
     */
    public static CoverageInformationItem parse(String outputMessage)
    {

        // "  line 84, col 32 to line 85, col 73 of module AtomicBakery: 1012492"
        outputMessage = outputMessage.trim();
        int[] index = { outputMessage.indexOf(LINE), outputMessage.indexOf(MOD), outputMessage.indexOf(COLON) };
        return new CoverageInformationItem(outputMessage.substring(index[1] + MOD.length(), index[2]), outputMessage
                .substring(index[0], index[1]), Long.parseLong(outputMessage.substring(index[2] + COLON.length())));
    }

    private final static String LINE = "line";
    private final static String MOD = " of module ";
    private final static String COLON = ": ";
    private final static String AT = "at ";

    public static String parseCoverageTimestamp(String outputMessage)
    {

        return outputMessage.substring(outputMessage.lastIndexOf(AT) + AT.length());
    }

}
