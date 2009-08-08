package org.lamport.tla.toolbox.ui.handler;

import java.util.HashMap;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.wizard.NewSpecWizard;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Command handler for new Specifications
 * 
 * @author zambrovski
 */
public class NewSpecHandler extends AbstractHandler implements IHandler
{

    public static final String COMMAND_ID = "toolbox.command.spec.new";

    /**
     * @see org.eclipse.core.commands.AbstractHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        IWorkbenchWindow window = HandlerUtil.getActiveWorkbenchWindowChecked(event);

        // Create the wizard
        NewSpecWizard wizard = new NewSpecWizard();
        // we pass null for structured selection, cause we just not using it
        wizard.init(window.getWorkbench(), null);
        Shell parentShell = window.getShell();
        // Create the wizard dialog
        WizardDialog dialog = new WizardDialog(parentShell, wizard);
        dialog.setHelpAvailable(true);
        
        // Open the wizard dialog
        if (Window.OK == dialog.open())
        {
            // read the spec from the wizard and put as parameter
            Spec spec = wizard.getSpec();
            
            // create parameters for the handler
            HashMap parameters = new HashMap();
            parameters.put(OpenSpecHandler.PARAM_SPEC, spec.getName());

            // runs the command
            UIHelper.runCommand(OpenSpecHandler.COMMAND_ID, parameters);
        }


        return null;
    }
}
