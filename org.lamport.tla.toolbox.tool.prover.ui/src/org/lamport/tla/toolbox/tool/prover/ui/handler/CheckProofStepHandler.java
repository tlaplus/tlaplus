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

public class CheckProofStepHandler extends AbstractHandler
{
    public static final String COMMAND_ID = "org.lamport.tla.toolbox.tool.prover.ui.checkProof";
    /**
     * Name of the module name to be checked.
     */
    public static final String PARAM_MODULE_NAME = "org.lamport.tla.toolbox.tool.prover.ui.paramModuleName";
    /**
     * Line number of the step to be checked.
     */
    public static final String PARAM_LINE_NUMBER = "org.lamport.tla.toolbox.tool.prover.ui.paramLineNumber";

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        try
        {
            /*
             * Retrieve the module name and the line
             * number from the execution event.
             */
            String moduleName = event.getParameter(PARAM_MODULE_NAME);
            int lineNumber = Integer.parseInt(event.getParameter(PARAM_LINE_NUMBER));

            if (moduleName != null)
            {
                IResource module = ResourceHelper.getResourceByModuleName(moduleName);
                if (module != null)
                {

                    ILaunchConfigurationWorkingCopy config = DebugPlugin.getDefault().getLaunchManager()
                            .getLaunchConfigurationType(ProverLaunchDelegate.CONFIG_TYPE).newInstance(
                                    ToolboxHandle.getCurrentSpec().getProject(), module.getFullPath().toOSString());

                    config.setAttribute(ProverLaunchDelegate.MODULE_PATH, module.getRawLocation().toPortableString());

                    config.setAttribute(ProverLaunchDelegate.LINE_NUMBER, lineNumber);
                    
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
