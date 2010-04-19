package org.lamport.tla.toolbox.tool.prover.launch;

import org.eclipse.core.runtime.IPath;

public interface IProverConfigurationConstants
{
    
    /**
     * The full file system path to the module.
     * 
     * This path should be produced by a call
     * to {@link IPath#toPortableString()}.
     */
    public static String MODULE_PATH = "modulePath";
    
    /**
     * The line number of the step to be checked.
     */
    public static String LINE_NUMBER = "lineNumber";

}
