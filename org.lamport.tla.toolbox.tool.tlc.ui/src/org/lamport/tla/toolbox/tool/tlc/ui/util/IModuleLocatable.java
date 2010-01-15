package org.lamport.tla.toolbox.tool.tlc.ui.util;

import org.lamport.tla.toolbox.tool.tlc.output.data.CoverageInformationItem;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCState;

import tla2sany.st.Location;

/**
 * All implementing classes should have a corresponding location
 * within a module.
 * 
 * Currently this is implemented by {@link TLCState} and {@link CoverageInformationItem}
 * because they both have a corresponding action in a module.
 * @author Daniel Ricketts
 *
 */
public interface IModuleLocatable
{

    public Location getModuleLocation();

}
