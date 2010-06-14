package org.lamport.tla.toolbox.tool.tlc.ui.util;

import org.lamport.tla.toolbox.tool.tlc.output.data.CoverageInformationItem;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCState;

import tla2sany.st.Location;

/**
 * All implementing classes should have a corresponding location
 * within a module and a model name. The model name should correspond to
 * the name of the model that was run to create the implementing class.
 * 
 * Currently this is implemented by {@link TLCState} and {@link CoverageInformationItem}
 * because they both have a corresponding action in a module.
 * @author Daniel Ricketts
 *
 */
public interface IModuleLocatable
{

    /**
     * The {@link Location} in the module.
     * @return
     */
    public Location getModuleLocation();

    /**
     * The name of the model.
     * 
     * @return
     */
    public String getModelName();

}
