package org.lamport.tla.toolbox.tool.tlc.launch;

/**
 * Constants for the configuration
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IConfigurationConstants
{
    /**
     * path to the root file of the spec (/bar/foo.tla)
     */
    public static final String SPEC_ROOT_FILE = "specRootFile";
    /**
     * Name of the root module (foo)
     */
    public static final String SPEC_ROOT_MODULE = "specRootModule";
    /**
     * name of the spec (foo_spec) 
     */
    public static final String SPEC_NAME = "specName";
    /**
     * Name of the configuration (foo_mc_{i})
     */
    public static final String MODEL_NAME = "configurationName";
    /**
     * Path to the file to model check (/bar/foo_mc_{i}.tla from spec foo)
     */
    public static final String MODEL_ROOT_FILE = "modelRootFile";
    /**
     * Path to the config file (/bar/foo_mc_{i}.cfg)
     */
    public static final String CONFIG_FILE = "configFile";
    /**
     * Number of workers to use during TLC launch
     */
    public static final String LAUNCH_NUMBER_OF_WORKERS = "numberOfWorkers";
    /**
     * How to run TLC (model-checking = true, simulation = false)
     */
    public static final String LAUNCH_MC_MODE = "mcMode";
    /**
     * the VIEW to map from variables to values
     */
    public static final String LAUNCH_VIEW = "view";
    /**
     * MC depth first 
     */
    public static final String LAUNCH_DFID_MODE = "dfidMode";
    /**
     * the depth of DFID run 
     */
    public static final String LAUNCH_DFID_DEPTH = "dfidDepth";
    /**
     * the depth of simulation run 
     */
    public static final String LAUNCH_SIMU_DEPTH = "simuDepth";
    /**
     * the aril of simulation run 
     */
    public static final String LAUNCH_SIMU_ARIL = "simuAril";
    /**
     * the seed of simulation run 
     */
    public static final String LAUNCH_SIMU_SEED = "simuSeed";
}
