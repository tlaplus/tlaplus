package org.lamport.tla.toolbox.tool.tlc.launch.ui;

/**
 * Constants for the configuration
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IConfigurationConstants
{
    // public static final String SPEC_ROOT_FOLDER = "specRootFolder";
    /**
     * path to the config file
     */
    public static final String CONFIG_FILE = "configFile";
    /**
     * path to the root file
     */
    public static final String SPEC_ROOT_FILE = "specRootFile";

    /**
     * name of the spec
     */
    public static final String SPEC_NAME = "specName";
    /**
     * Name of the file to model check (usually foo_mc_1 from spec foo)
     */
    public static final String MODEL_ROOT_FILE = "modelRootFile";

}
