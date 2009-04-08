package org.lamport.tla.toolbox.tool.tlc.launch;


/**
 * Collection of constant default values
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IConfigurationDefaults
{
    /**
     * Empty string
     */
    public static final String EMPTY_STRING = "";
    
    public static final int LAUNCH_NUMBER_OF_WORKERS_DEFAULT = 2;
    
    /**
     * Default is the model-checking mode
     */
    public static final boolean LAUNCH_MC_MODE_DEFAULT = true;
    
    /**
     * Breadth first is default
     */
    public static final boolean LAUNCH_DFID_MODE_DEFAULT = false;

    public static final int LAUNCH_DFID_DEPTH_DEFAULT = 100;
    public static final int LAUNCH_SIMU_DEPTH_DEFAULT = 100;
    public static final int LAUNCH_SIMU_ARIL_DEFAULT = -1;
    public static final int LAUNCH_SIMU_SEED_DEFAULT = -1;
    
    
    
}
