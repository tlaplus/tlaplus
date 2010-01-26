package org.lamport.tla.toolbox.tool.tlc.traceexplorer;

import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;

import org.eclipse.debug.core.ILaunchConfiguration;

/**
 * This class should not longer be used.
 * 
 * This class contains TLC error traces for launch
 * configurations. Up to one trace can be stored for each launch configuration.
 * 
 * This class is a singleton. The access method is {@link TLCErrorTraceRegistry#getErrorTraceRegistry()}.
 * Traces are added by calling {@link TLCErrorTraceRegistry#addTLCErrorTrace(ILaunchConfiguration, List)}. Traces
 * are retrieved by calling {@link TLCErrorTraceRegistry#getTrace(ILaunchConfiguration)}.
 * 
 * Traces are lists of {@link SimpleTLCState}. This class is currently used because the storage
 * of traces occurs in a class in the tlc UI plug-in which we cannot directly access from the
 * tlc plug-in. Thus, traces must be added from the UI plug-in to this class using {@link SimpleTLCState}
 * because that class is in this plug-in.
 * 
 * @author Daniel Ricketts
 *
 *@deprecated
 */
public class TLCErrorTraceRegistry
{

    // hashtable containing the traces
    // key is the name of the config file representing
    // the model for the trace
    private Hashtable traces;
    // singleton instance
    private static TLCErrorTraceRegistry instance;

    /**
     * Adds a trace to the registry for the launch configuration. Replaces
     * the previous trace (if there is one) for this config. The trace should
     * be a List of arrays of {@link SimpleTLCState}. If it is not, it will not be
     * added.
     * 
     * @param config
     * @param trace
     */
    public void addTLCErrorTrace(ILaunchConfiguration config, List trace)
    {

        Iterator it = trace.iterator();
        while (it.hasNext())
        {
            if (!(it.next() instanceof SimpleTLCState))
            {
                // do not add trace if all elements are not SimpleTLCState
                return;
            }
        }
        // trace is allowed
        traces.put(config.getName(), trace);
    }

    /**
     * Returns a list of {@link SimpleTLCState} representing the error
     * trace for the config, or null if none is found.
     * 
     * @param config
     * @return
     */
    public List getTrace(ILaunchConfiguration config)
    {
        return (List) traces.get(config.getName());
    }

    /**
     * Clients should use {@link TLCErrorTraceRegistry#getErrorTraceRegistry()} to access
     * the singleton instance of this class.
     */
    private TLCErrorTraceRegistry()
    {
        traces = new Hashtable();
    }

    /**
     * Access method for error trace registry.
     * 
     * @return
     */
    public static TLCErrorTraceRegistry getErrorTraceRegistry()
    {
        if (instance == null)
        {
            instance = new TLCErrorTraceRegistry();
        }
        return instance;
    }
}
