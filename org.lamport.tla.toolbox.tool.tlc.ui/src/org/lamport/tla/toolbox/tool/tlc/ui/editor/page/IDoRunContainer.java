package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

/**
 * Interface for running
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IDoRunContainer
{

    // modes
    public static final String MODE_RUN = "run";
    public static final String MODE_DEBUG = "debug";
    
    public void doRun(String mode);

}