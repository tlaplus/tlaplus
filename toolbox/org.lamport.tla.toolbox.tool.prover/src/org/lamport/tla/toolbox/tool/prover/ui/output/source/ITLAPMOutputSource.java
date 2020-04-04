package org.lamport.tla.toolbox.tool.prover.ui.output.source;

import org.eclipse.core.runtime.IPath;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.TLAPMMessage;

/**
 * This is a source of data from the output of the
 * TLAPM for a single module given by {@link ITLAPMOutputSource#getFullModulePath()}.
 * Listeners can be added by calling {@link ITLAPMOutputSource#addListener(ITLAPMOutputSourceListener)}.
 * However, this method should not be called directly by listeners. Listeners
 * should register themselves using the singleton instance of the {@link TLAPMOutputSourceRegistry}
 * using the method {@link TLAPMOutputSourceRegistry#addListener(ITLAPMOutputSourceListener)}.
 * 
 * This interface is not used.
 * 
 * @author Daniel Ricketts
 *
 */
public interface ITLAPMOutputSource
{

    public void addListener(ITLAPMOutputSourceListener listener);

    public void removeListener(ITLAPMOutputSourceListener listener);

    /**
     * The full file system path to the module for which this source contains
     * output.
     * 
     * @return
     */
    public IPath getFullModulePath();

    /**
     * Returns the array of {@link ITLAPMOutputSourceListener}'s currently
     * listening to this source.
     * 
     * @return
     */
    public ITLAPMOutputSourceListener[] getListeners();

    /**
     * Called to notify this source of a new instance
     * of {@link ITLAPMData}.
     * 
     * @param data
     */
    public void newData(TLAPMMessage data);

    /**
     * Notifies the source that no more data is to be sent.
     */
    public void onDone();

}
