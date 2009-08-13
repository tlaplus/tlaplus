package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.Vector;

/**
 * Container TLC region
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCRegionContainer extends TLCRegion
{
    
    private Vector subRegions = new Vector();
    
    /**
     * Constructs the container type
     * @param offset
     * @param length
     */
    public TLCRegionContainer(int offset, int length)
    {
        super(offset, length);
    }
    
    public TLCRegion[] getSubRegions()
    {
        return (TLCRegion[]) subRegions.toArray(new TLCRegion[subRegions.size()]);
    }

    
    public void setSubRegions(Vector elements)
    {
        this.subRegions = elements;
    }
}
