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
     * The beginning line of the location being passed
     * to the prover.
     * 
     * -1 means the entire module is the location.
     */
    public static String BEGIN_LINE = "bl";
    /**
     * The beginning column of the location being passed
     * to the prover.
     * 
     * -1 means the entire module is the location.
     */
    public static String BEGIN_COLUMN = "bc";
    /**
     * The end line of the location being passed
     * to the prover.
     * 
     * -1 means the entire module is the location.
     */
    public static String END_LINE = "el";
    /**
     * The beginning line of the location being passed
     * to the prover.
     * 
     * -1 means the entire module is the location.
     */
    public static String END_COLUMN = "ec";

}
