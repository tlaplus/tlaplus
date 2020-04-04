package org.lamport.tla.toolbox.tool.tlc.output;

import org.lamport.tla.toolbox.tool.tlc.model.Model;

/**
 * Basic interface for the sink
 * @author Simon Zambrovski
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
     * Trace explorer output stream
     */
    public final static int TYPE_TRACE_EXPLORE = 3;
    /**
     * Extension point, the interface is used in
     */
    public static final String EXTENSION_ID = "org.lamport.tla.toolbox.tlc.processOutputSink";

    /**
     * Appends text to the sink
     * @param text 
     */
    public void appendText(String text);

    /**
     * Called prior the usage to initialize the sink
     * @param model name of the process
     * @param sinkType type, see constants {@link IProcessOutputSink#TYPE_DEBUG}, {@link IProcessOutputSink#TYPE_ERROR}, {@link IProcessOutputSink#TYPE_OUT}, {@link IProcessOutputSink#TYPE_TRACE_EXPLORE}
     */
    public void initializeSink(Model model, int sinkType);

    /**
     * Signal to the sink that the process has terminated and no data will be sent
     */
    public void processFinished();
}
