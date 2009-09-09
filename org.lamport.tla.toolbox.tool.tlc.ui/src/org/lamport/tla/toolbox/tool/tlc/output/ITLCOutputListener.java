package org.lamport.tla.toolbox.tool.tlc.output;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITypedRegion;

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
     * Reports new output
     */
    public void onOutput(ITypedRegion region, IDocument document);

    /**
     * Reports end of output
     */
    public void onDone();

    /**
     * Informs the listener that a new source has replaced an existing source.
     */
    public void onNewSource();
}
