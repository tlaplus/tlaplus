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
     * name of the spec (foo) 
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
    
    

}
