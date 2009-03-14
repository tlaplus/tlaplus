package org.lamport.tla.toolbox.tool;

/**
 * Exception thrown during tool initialization or termination
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ToolLifecycleException extends Exception
{
    private static final long serialVersionUID = 6237014663324928734L;

    public ToolLifecycleException(String message)
    {
        super(message);
    }
}
