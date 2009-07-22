package org.lamport.tla.toolbox.tool.tlc.output;

/**
 * Basic interface for the sink
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IProcessOutputSink
{
    /**
     * Debug stream
     */
    public final static int TYPE_DEBUG = -1;
    /**
     * Output stream
     */
    public final static int TYPE_OUT = 1;
    /**
     * Error stream 
     */
    public final static int TYPE_ERROR = 2;

    /**
     * Appends text to the sink
     * @param text 
     */
    public void appendText(String text);
    
    /**
     * Called prior the usage to initialize the sink
     * @param processName name of the process
     * @param sinkType type, see constants {@link IProcessOutputSink#TYPE_DEBUG}, {@link IProcessOutputSink#TYPE_ERROR}, {@link IProcessOutputSink#TYPE_OUT}
     */
    public void initializeSink(String processName, int sinkType);
    
    /**
     * Signal to the sink that the process has terminated and no data will be sent
     */
    public void processFinished();
}
