package org.lamport.tla.toolbox.tool.tlc.launch;

import tlc2.tool.fp.FPSet;

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
     * Which profile to use for TLC configuration
     */
    public static final String TLC_RESOURCES_PROFILE = "tlcResourcesProfile";
    /**
     * Number of workers to use during TLC launch
     */
    public static final String LAUNCH_NUMBER_OF_WORKERS = "numberOfWorkers";
    /**
     * Launch distributed version of TLC
     */
	public static final String LAUNCH_DISTRIBUTED = "distributedTLC";
    /**
     * Launch distributed version of TLC and send result to this address
     */
	public static final String LAUNCH_DISTRIBUTED_RESULT_MAIL_ADDRESS = "result.mail.address";
    /**
     * Additional VM args for distributed version of TLC
     */
	public static final String LAUNCH_JVM_ARGS = "distributedTLCVMArgs";
    /**
     * Additional VM args for distributed version of TLC
     */
	public static final String LAUNCH_TLC_PARAMETERS = "TLCCmdLineParameters";
    /**
     * Distributed FPSets
     */
	public static final String LAUNCH_DISTRIBUTED_FPSET_COUNT = "distributedFPSetCount";
    /**
     * Distributed Nodes count
     */
	public static final String LAUNCH_DISTRIBUTED_NODES_COUNT = "distributedNodesCount";
	/**
	 * Network interface under which TLC server process will listen (java.rmi.server.hostname)
	 */
	public static final String LAUNCH_DISTRIBUTED_INTERFACE = "distributedNetworkInterface";
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
     * Choose FP index randomly
     */
    public static final String LAUNCH_FP_INDEX_RANDOM = "fpIndexRandom";

    /**
	 * Defers verification of liveness properties upon the final stage of model
	 * checking (upon termination).
	 */
    public static final String LAUNCH_DEFER_LIVENESS = "deferLiveness";
    /**
	 * Visualize state graph after model checking with GraphViz.
	 */
    public static final String LAUNCH_VISUALIZE_STATEGRAPH = "visualizeStateGraph";
    /**
	 * Collect coverage statistics
	 */
    public static final String LAUNCH_COVERAGE = "collectCoverage";
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
     * The maximum size (upper bound) for a TLA set
     */
    public static final String LAUNCH_MAXSETSIZE = "maxSetSize";
    
    /**
     * {@link FPSet} implementation to use during model checking
     */
    public static final String LAUNCH_FPSET_IMPL = "fpSetImpl";

}
