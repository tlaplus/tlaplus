package org.lamport.tla.toolbox.tool;

/**
 * Exception thrown during tool initialization
 * @author zambrovski
 */
public class ToolInitializationException extends Exception
{
    private static final long serialVersionUID = 6237014663324928734L;

    public ToolInitializationException(String message)
    {
        super(message);
    }
}
