package org.lamport.tla.toolbox.tool.prover.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.prover.launch.ProverLaunchDelegate;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Checks the proof of a specific location in a module or of the entire
 * module if the location is not specified through parameters.
 * 
 * The command associated with this handler has one required parameter,
 * the module name, and four optional parameters, begin line, begin column,
 * end line, end column.
 * 
 * @author Daniel Ricketts
 *
 */
public class CheckProofHandler extends AbstractHandler
{
    public static final String COMMAND_ID = "org.lamport.tla.toolbox.tool.prover.ui.checkProof";
    /**
     * Name of the module name to be checked.
     */
    public static final String PARAM_MODULE_NAME = "org.lamport.tla.toolbox.tool.prover.ui.paramModuleName";
    /**
     * Begin line number of the location to be checked.
     */
    public static final String PARAM_BEGIN_LINE = "org.lamport.tla.toolbox.tool.prover.ui.paramBeginLine";
    /**
     * Begin column of the location to be checked.
     */
    public static final String PARAM_BEGIN_COLUMN = "org.lamport.tla.toolbox.tool.prover.ui.paramBeginColumn";
    /**
     * End line of the location to be checked.
     */
    public static final String PARAM_END_LINE = "org.lamport.tla.toolbox.tool.prover.ui.paramEndLine";
    /**
     * End column of the location to be checked.
     */
    public static final String PARAM_END_COLUMN = "org.lamport.tla.toolbox.tool.prover.ui.paramEndColumn";

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        try
        {
            // prompt to save any unsaved resources
            // the module open in the active editor could be dependent upon
            // any open module
            boolean proceed = UIHelper.promptUserForDirtyModules();
            if (!proceed)
            {
                return null;
            }

            /*
             * Retrieve the module name from the execution event.
             */
            String moduleName = event.getParameter(PARAM_MODULE_NAME);

            /*
             * Try to retrieve the location from the parameters.
             * 
             * Setting any of the coordinates to -1 indicates
             * to the prover launch delegate that the entire module
             * should be checked.
             */
            String beginLineString = event.getParameter(PARAM_BEGIN_LINE);
            String beginColumnString = event.getParameter(PARAM_BEGIN_COLUMN);
            String endLineString = event.getParameter(PARAM_END_LINE);
            String endColumnString = event.getParameter(PARAM_END_COLUMN);

            int beginLine = -1;
            int beginColumn = -1;
            int endLine = -1;
            int endColumn = -1;

            if (beginLineString != null)
            {
                beginLine = Integer.parseInt(beginLineString);
            }

            if (beginColumnString != null)
            {
                beginColumn = Integer.parseInt(beginColumnString);
            }

            if (endLineString != null)
            {
                endLine = Integer.parseInt(endLineString);
            }

            if (endColumnString != null)
            {
                endColumn = Integer.parseInt(endColumnString);
            }

            if (moduleName != null)
            {
                IResource module = ResourceHelper.getResourceByModuleName(moduleName);
                if (module != null)
                {

                    ILaunchConfigurationWorkingCopy config = DebugPlugin.getDefault().getLaunchManager()
                            .getLaunchConfigurationType(ProverLaunchDelegate.CONFIG_TYPE).newInstance(
                                    ToolboxHandle.getCurrentSpec().getProject(), module.getFullPath().toOSString());

                    config.setAttribute(ProverLaunchDelegate.MODULE_PATH, module.getRawLocation().toPortableString());

                    config.setAttribute(ProverLaunchDelegate.BEGIN_LINE, beginLine);

                    config.setAttribute(ProverLaunchDelegate.BEGIN_COLUMN, beginColumn);

                    config.setAttribute(ProverLaunchDelegate.END_LINE, endLine);

                    config.setAttribute(ProverLaunchDelegate.END_COLUMN, endColumn);

                    config.launch(ProverLaunchDelegate.MODE_CHECK_STEP, new NullProgressMonitor());

                } else
                {
                    System.out.println("Module name does not correspond to a module in the current project.");
                }
            }
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (NumberFormatException e)
        {
            e.printStackTrace();
        }
        return null;
    }

}
