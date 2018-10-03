package org.lamport.tla.toolbox.tool.tlc.output.data;

import org.lamport.tla.toolbox.tool.tlc.ui.util.IModuleLocatable;

import tla2sany.st.Location;
import tlc2.TLCGlobals;

/**
 * Coverage information item
 * @author Simon Zambrovski
 * @version $Id$
 */
public class CoverageInformationItem implements IModuleLocatable
{
    private final static String MOD = " of module ";
    private final static String COLON = ": ";
    private final static String AT = "at ";

    private String locationString;
    private Location location;
    private String modelName;
    private long count;
	private int layer;

    /**
     * Creates an simple item storing information about a coverage at a certain location
     * @param location
     * @param count
     * @param modelName the name of the model for which this is coverage information
     * @param module
     */

    private CoverageInformationItem(Location location, long count, String modelName, int layer)
    {
        this.location = location;
        this.locationString = this.location.toString();
        this.count = count;
        this.modelName = modelName;
        this.layer = layer;
    }

    public final String getModule()
    {
        return locationString.substring(locationString.indexOf(MOD) + MOD.length());
    }

    public final String getLocation()
    {
        return locationString.substring(0, locationString.indexOf(MOD));
    }

    public final long getCount()
    {
        return count;
    }

	/**
	 * If two CCI are co-located (overlapping, nested, ...), the layer indicates
	 * which one is considered more important.
	 */
	public int getLayer() {
		return layer;
	}

    /**
     * Parses the coverage information item from a string
     * @param outputMessage
     * @param modelName the name of the model for which this is coverage information
     * @return
     */
    public static CoverageInformationItem parse(String outputMessage, String modelName)
    {

        // "  line 84, col 32 to line 85, col 73 of module AtomicBakery: 1012492"
        outputMessage = outputMessage.trim();
        
        final int layer = outputMessage.lastIndexOf(TLCGlobals.coverageIndent) + 1;
        
        int index = outputMessage.indexOf(COLON);
        return new CoverageInformationItem(Location.parseLocation(outputMessage.substring(layer, index)), Long
                .parseLong(outputMessage.substring(index + COLON.length())), modelName, layer);
    }

    /**
     * Parses coverage timestamp from the string  
     * @param outputMessage
     * @return
     */
    public static String parseCoverageTimestamp(String outputMessage)
    {
        return outputMessage.substring(outputMessage.lastIndexOf(AT) + AT.length());
    }

    /**
     * The {@link Location} in the module.
     * @return
     */
    public Location getModuleLocation()
    {
        return location;
    }

    /**
     * The name of the model.
     * 
     * @return
     */
    public String getModelName()
    {
        return modelName;
    }

}
