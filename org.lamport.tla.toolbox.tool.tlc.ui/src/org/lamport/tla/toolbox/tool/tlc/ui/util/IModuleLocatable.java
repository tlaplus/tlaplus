package org.lamport.tla.toolbox.tool.tlc.ui.util;

import tla2sany.st.Location;

/**
 * All implementing classes should have a corresponding location
 * within a module.
 * 
 * Currently this is implemented by TLAState and CoverageInformationItem
 * because they both have a corresponding action in a module.
 * @author Daniel Ricketts
 *
 */
public interface IModuleLocatable
{

    public Location getModuleLocation();

}
