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
     * name of the spec (foo_spec) 
     */
    public static final String SPEC_NAME = "specName";
    /**
     * Name of the configuration (foo_mc_{i})
     */
    public static final String MODEL_NAME = "configurationName";
    /**
     * Number of workers to use during TLC launch
     */
    public static final String LAUNCH_NUMBER_OF_WORKERS = "numberOfWorkers";
    /**
     * Launch distributed version of TLC
     */
	public static final String LAUNCH_DISTRIBUTED = "distributedTLC";
    /**
     * Additional VM args for distributed version of TLC
     */
	public static final String LAUNCH_DISTRIBUTED_ARGS = "distributedTLCVMArgs";
    /**
     * Pre-flight script (primarily for distributed version of TLC)
     */
	public static final String LAUNCH_DISTRIBUTED_SCRIPT = "distributedTLCScript";
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
    /**
     * the fp seed index "-fp" 
     */
    public static final String LAUNCH_FP_INDEX = "fpIndex";

    /**
     * Run from the checkpoint
     */
    public static final String LAUNCH_RECOVER = "recover";

    /**
     * JVM maximum heap size
     */
    public static final String LAUNCH_MAX_HEAP_SIZE = "maxHeapSize";

    /**
     * Amount of fp bits used for disk storage addressing
     */
    public static final String LAUNCH_FPBITS = "fpBits";

    /**
     * Length of time in minutes the TLC must run
     * before the model is automatically locked at the termination
     * of the run.
     */
    public static final String LAUNCH_AUTO_LOCK_MODEL_TIME = "autoLockTime";

}
