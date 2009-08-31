package org.lamport.tla.toolbox.tool.tlc.output;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITypedRegion;

/**
 * A listener interested in TLC Output status changes for a particular TLC process
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface ITLCOutputListener
{
    /**
     * Retrieves the process name of TLC 
     * @return the name to identify the TLC instance
     */
    public String getProcessName();

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
