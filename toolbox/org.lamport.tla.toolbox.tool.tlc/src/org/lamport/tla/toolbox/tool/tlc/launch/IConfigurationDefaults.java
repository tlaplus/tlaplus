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

    /**
     * Default number of workers.  Was set by Simon to be is 2.
     * Modified by LL on 11 October 2009 to be half the number of available processors.
     * Fixed by LL on 20 Oct 2009 to equal 1, not 0, if there is only 1 available processor.
     * 
     * 20190302 - this will be deprecated in the future once TLCConsumptionProfile is fully adopted.
     */
    public static final int LAUNCH_NUMBER_OF_WORKERS_DEFAULT = (Runtime.getRuntime().availableProcessors() > 1) ? (Runtime
            .getRuntime().availableProcessors() / 2)
            : 1;

	/**
	 * Run in distributed mode?
	 * 
	 * We need two, because in some places we especially want to specify "do not launch remote workers" and will be
	 * 	shafted should some future developer change the default value.
	 */
    public static final String LAUNCH_DISTRIBUTED_NO = "off";
	public static final String LAUNCH_DISTRIBUTED_DEFAULT = LAUNCH_DISTRIBUTED_NO;
	
    /**
     * Launch distributed version of TLC and send result to this address
     */
	public static final String LAUNCH_DISTRIBUTED_RESULT_MAIL_ADDRESS_DEFAULT = "";
	
	/**
	 * Distributed FPSet default count
	 */
	public static final int LAUNCH_DISTRIBUTED_FPSET_COUNT_DEFAULT = 0;
	
	/**
	 * Distributed nodes default count
	 */
	public static final int LAUNCH_DISTRIBUTED_NODES_COUNT_DEFAULT = 1;
	
	/**
	 * Additional (e.g. RMI specific) VM args for distributed model checker
	 */
	public static final String LAUNCH_JVM_ARGS_DEFAULT = "";
	/**
	 * Additional TLC cmdline parameters
	 */
	public static final String LAUNCH_TLC_PARAMETERS_DEFAULT = "";
	
	/**
	 * Additional script for distributed model checker
	 */
	public static final String LAUNCH_DISTRIBUTED_SCRIPT_DEFAULT = "";
	
    /**
     * Default max heap size
     * Now set as a preference in TLCPreferencePage
     */
    /*
    public static final int LAUNCH_MAX_HEAP_SIZE_DEFAULT = 500;*/

    /**
     * Default is the model-checking mode
     */
    public static final boolean LAUNCH_MC_MODE_DEFAULT = true;

    /**
     * Breadth first is default
     */
    public static final boolean LAUNCH_DFID_MODE_DEFAULT = false;

    /** 
     * Default depth for DFID MC is 100 
     */
    public static final int LAUNCH_DFID_DEPTH_DEFAULT = 100;
    /** 
     * Default depth for Simulation is 100 
     */
    public static final int LAUNCH_SIMU_DEPTH_DEFAULT = 100;
    /** 
     * Default aril is -1 
     */
    public static final int LAUNCH_SIMU_ARIL_DEFAULT = -1;
    /** 
     * Default seed is -1 
     */
    public static final int LAUNCH_SIMU_SEED_DEFAULT = -1;
    /** 
     * Default fp seed is 1 meaning the first elem in the list 
     */
    public static final int LAUNCH_FP_INDEX_DEFAULT = 1;
    /** 
     * Default fp seed is 1 meaning the first elem in the list 
     */
    public static final boolean LAUNCH_FP_INDEX_RANDOM_DEFAULT = true;
    /** 
     * Default fp seed is 1 meaning the first elem in the list 
     */
    public static final boolean LAUNCH_DEFER_LIVENESS_DEFAULT = false;
    /**
     * Do not visualize state graph by default. Most state graphs are too large. 
     */
    public static final boolean LAUNCH_VISUALIZE_STATEGRAPH_DEFAULT = false;
    /**
     * Do not recover from checkpoints by default
     */
    public static final boolean LAUNCH_RECOVER_DEFAULT = false;
    /**
     * Collect coverage and cost statistics by default
     */
    public static final int LAUNCH_COVERAGE_DEFAULT = 1;
}
