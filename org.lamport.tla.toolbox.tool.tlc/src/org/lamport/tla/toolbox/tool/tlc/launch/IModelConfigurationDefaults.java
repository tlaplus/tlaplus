package org.lamport.tla.toolbox.tool.tlc.launch;

/**
 * Defaults for the model configuration
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IModelConfigurationDefaults extends IConfigurationDefaults
{
    /**
     * Default if the closed specification is used
     */
    public static final boolean MODEL_BEHAVIOR_IS_CLOSED_SPEC_USED_DEFAULT = true;
    
    /**
     * Default for checking the deadlock
     */
    public static final boolean MODEL_CORRECTNESS_CHECK_DEADLOCK_DEFAULT = false;

}
