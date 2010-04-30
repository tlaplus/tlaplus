package org.lamport.tla.toolbox.tool.prover.ui.output.source;

import org.eclipse.core.runtime.IPath;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.TLAPMMessage;

/**
 * Interface for listening to data from TLAPM
 * output.
 * 
 * @author Daniel Ricketts
 *
 */
public interface ITLAPMOutputSourceListener
{

    /**
     * Passes new {@link ITLAPMData} to the listener.
     * 
     * @param data
     */
    public void newData(TLAPMMessage data);

    /**
     * The full file system path for which this
     * listener wants to receive TLAPM output.
     * 
     * @return
     */
    public IPath getFullModulePath();

    /**
     * Called to dispose of the listener when
     * it is no longer needed.
     */
    public void dispose();

}
