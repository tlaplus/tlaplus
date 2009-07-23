package org.lamport.tla.toolbox.tool;


/**
 * Exception thrown during toolbox initialization or termination
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ToolboxLifecycleException extends Exception
{
    private static final long serialVersionUID = 6237014663324928734L;

    public ToolboxLifecycleException(String message)
    {
        super(message);
    }

    public ToolboxLifecycleException(String message, Throwable cause)
    {
        super(message, cause);
    }
}
