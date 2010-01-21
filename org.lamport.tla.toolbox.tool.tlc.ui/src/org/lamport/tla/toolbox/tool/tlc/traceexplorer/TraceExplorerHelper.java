package org.lamport.tla.toolbox.tool.tlc.traceexplorer;

import java.util.Iterator;
import java.util.List;

import org.eclipse.debug.core.ILaunchConfiguration;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;

/**
 * Provides utility methods for the trace explorer
 * @author Daniel Ricketts
 *
 */
public class TraceExplorerHelper
{

    /**
     * Returns the trace most recently produced by running model checking
     * on the config or null if none found.
     * 
     * @param config
     * @return
     */
    public static List getOriginalTrace(ILaunchConfiguration config)
    {
        /*
         * The trace explorer should not be run for a model while TLC is being run for
         * model checking on that model. Therefore, the original trace can be retrieved
         * from the tlc output source registry for model checking.
         */
        TLCModelLaunchDataProvider originalTraceProvider = TLCOutputSourceRegistry.getModelCheckSourceRegistry()
                .getProvider(config);
        List errors = originalTraceProvider.getErrors();
        if (errors != null)
        {
            Iterator it = errors.iterator();
            while (it.hasNext())
            {
                TLCError error = (TLCError) it.next();
                if (error.hasTrace())
                {
                    return error.getStates();
                }
            }
        }

        // no trace found
        return null;
    }

}
