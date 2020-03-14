package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.Vector;

import org.eclipse.jface.text.ITypedRegion;

/**
 * Container TLC region
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCRegionContainer extends TLCRegion
{

    private Vector<ITypedRegion> subRegions = new Vector<ITypedRegion>();

    /**
     * Constructs the container type
     * @param offset
     * @param length
     */
    public TLCRegionContainer(int offset, int length)
    {
        super(offset, length);
    }

    public ITypedRegion[] getSubRegions()
    {
        return (ITypedRegion[]) subRegions.toArray(new ITypedRegion[subRegions.size()]);
    }

    public void setSubRegions(Vector<ITypedRegion> elements)
    {
        this.subRegions = elements;
    }
}
