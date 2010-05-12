package org.lamport.tla.toolbox.tool.tlc.output;

import org.eclipse.jface.text.ITypedRegion;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCRegion;

/**
 * A listener interested in TLC Output status changes for a particular TLC process
 * <br>
 * This class is not intended to be implemented by the clients.<br>
 * This class is not intended to be subclassed by the clients.<br>
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface ITLCOutputListener
{
    /**
     * Retrieves the process name of TLC 
     * @return the name to identify the TLC instance
     */
    public String getTLCOutputName();

    /**
     * Reports new output.
     * 
     * The new output comes in the form
     * of an {@link ITypedRegion} and the text represented by the region. The region
     * was originally created to point to a document. using the region's offset and
     * length when the region was created. However, the document may have changed
     * since the region was created, so its offset and length may not correspond to
     * anything useful. For this reason, the text originally pointed to by the region
     * is passed in.
     * 
     * The type of the region is useful, and if it is a {@link TLCRegion}, then it could contain other
     * useful information.
     */
    public void onOutput(ITypedRegion region, String text);

    /**
     * Reports end of output
     */
    public void onDone();

    /**
     * Informs the listener that a new source has replaced an existing source.
     */
    public void onNewSource();
}
