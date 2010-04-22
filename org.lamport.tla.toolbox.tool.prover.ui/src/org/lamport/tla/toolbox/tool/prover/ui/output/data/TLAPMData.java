package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import org.eclipse.core.runtime.IPath;

/**
 * Abstract class for a piece of data from the output
 * of the TLAPM.
 * 
 * Contains the full file system path
 * to the module for which this contains data.
 * 
 * @author Daniel Ricketts
 *
 */
public abstract class TLAPMData
{
    protected IPath modulePath;

    public TLAPMData(IPath modulePath)
    {
        this.modulePath = modulePath;
    }

    public IPath getModulePath()
    {
        return modulePath;
    }

}
