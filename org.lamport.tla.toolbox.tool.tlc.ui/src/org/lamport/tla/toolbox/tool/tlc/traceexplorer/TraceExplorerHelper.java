package org.lamport.tla.toolbox.tool.tlc.traceexplorer;

import java.io.ByteArrayInputStream;
import java.util.Iterator;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCState;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError.Length;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

import tlc2.output.MP;

/**
 * Provides utility methods for the trace explorer
 * @author Daniel Ricketts
 *
 */
public class TraceExplorerHelper
{

    /**
     * Returns the error that has a trace most recently produced by running model checking
     * on the config or null if none found.
     * 
     * @param config
     * @return
     */
    public static TLCError getErrorOfOriginalTrace(ILaunchConfiguration config)
    {
        /*
         * The trace explorer should not be run for a model while TLC is being run for
         * model checking on that model. Therefore, the original trace can be retrieved
         * from the tlc output source registry for model checking.
         */
        TLCModelLaunchDataProvider originalTraceProvider = TLCOutputSourceRegistry.getModelCheckSourceRegistry()
                .getProvider(config);
        List<TLCError> errors = originalTraceProvider.getErrors();
        if (errors != null)
        {
            Iterator<TLCError> it = errors.iterator();
            while (it.hasNext())
            {
                TLCError error = it.next();
                if (error.hasTrace())
                {
                    return error;
                }
            }
        }

        // no trace found
        return null;
    }

    /**
     * Writes the trace to MC_TE.out.
     * @param trace
     */
    public static void serializeTrace(ILaunchConfiguration config)
    {
        try
        {
            List<TLCState> trace = getErrorOfOriginalTrace(config).getStates(Length.ALL);
            Assert.isNotNull(trace);
            Iterator<TLCState> it = trace.iterator();
            IFile traceSourceFile = ModelHelper.getTraceSourceFile(config);
            ModelHelper.createOrClearFiles(new IFile[] { traceSourceFile }, new NullProgressMonitor());
            while (it.hasNext())
            {
                traceSourceFile.appendContents(new ByteArrayInputStream((MP.DELIM + MP.STARTMSG + "0000" + MP.COLON
                        + MP.STATE + " " + MP.DELIM + "\n").getBytes()), IResource.FORCE | IWorkspace.AVOID_UPDATE,
                        new NullProgressMonitor());
                TLCState state = (TLCState) it.next();
                StringBuffer toAppend = new StringBuffer();
                toAppend.append(state.getStateNumber()).append(": ").append(state.getLabel()).append("\n").append(
                        state.toString());

                traceSourceFile.appendContents(new ByteArrayInputStream(toAppend.toString().getBytes()),
                        IResource.FORCE | IWorkspace.AVOID_UPDATE, new NullProgressMonitor());

                traceSourceFile.appendContents(new ByteArrayInputStream(
                        (MP.DELIM + MP.ENDMSG + "0000" + " " + MP.DELIM + "\n").getBytes()), IResource.FORCE
                        | IWorkspace.AVOID_UPDATE, new NullProgressMonitor());

            }
        } catch (CoreException e)
        {
            TLCUIActivator.getDefault().logError("Error writing trace contents to file", e);
        }
    }
}
