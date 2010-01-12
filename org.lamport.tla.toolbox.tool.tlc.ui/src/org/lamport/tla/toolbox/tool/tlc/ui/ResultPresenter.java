package org.lamport.tla.toolbox.tool.tlc.ui;

import java.util.List;
import java.util.Vector;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunch;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.TraceExplorerDelegate;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.result.IResultPresenter;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Responsible for presenting the TLC launch results
 * 
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ResultPresenter implements IResultPresenter
{

    public ResultPresenter()
    {
    }

    public void showResults(ILaunch launch)
    {
        /*
         * For trace exploration, just update the error view with the data
         * from the run of TLC for trace exploration. For model checking, open
         * the editor for that model, show the result page, and update the
         * data on the result page.
         * 
         * TODO Check if the model on which the trace explorer was run is still
         * the active model. It is possible that the user has switched models
         * in the short amount of time it takes to run the trace explorer.
         */
        if (launch.getLaunchMode().equals(TraceExplorerDelegate.MODE_TRACE_EXPLORE))
        {
            TLCModelLaunchDataProvider traceExplorerDataProvider = TLCOutputSourceRegistry
                    .getTraceExploreSourceRegistry().getProvider(launch.getLaunchConfiguration());
            try
            {
                List expressions = launch.getLaunchConfiguration().getAttribute(
                        IModelConfigurationConstants.TRACE_EXPLORE_EXPRESSIONS, new Vector());
                int x = 2;
            } catch (CoreException e)
            {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }

            TLCErrorView.updateErrorView(traceExplorerDataProvider, true);
        } else
        {
            ModelEditor editor = (ModelEditor) UIHelper.openEditor(ModelEditor.ID, launch.getLaunchConfiguration()
                    .getFile());
            if (editor != null)
            {
                editor.showResultPage();
            }
        }
    }

}
