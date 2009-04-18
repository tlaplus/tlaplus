package org.lamport.tla.toolbox.tool.tlc.launch;

/**
 * Defaults for the model configuration
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IModelConfigurationDefaults extends IConfigurationDefaults
{
    /**
     * constant for no spec
     */
    public static final int MODEL_BEHAVIOR_TYPE_NO_SPEC = 0;
    /**
     * constant for spec as a single formula
     */
    public static final int MODEL_BEHAVIOR_TYPE_SPEC_CLOSED = 1;
    /**
     * constant for spec as init, next fairness
     */
    public static final int MODEL_BEHAVIOR_TYPE_SPEC_INIT_NEXT = 2;

    
    /**
     * Default if the closed specification is used
     */
    public static final int MODEL_BEHAVIOR_TYPE_DEFAULT = MODEL_BEHAVIOR_TYPE_NO_SPEC;
    
    
    
    /**
     * Default for checking the deadlock
     */
    public static final boolean MODEL_CORRECTNESS_CHECK_DEADLOCK_DEFAULT = true;

}
