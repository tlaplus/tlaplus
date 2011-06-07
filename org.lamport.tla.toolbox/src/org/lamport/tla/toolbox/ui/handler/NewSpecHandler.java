package org.lamport.tla.toolbox.ui.handler;

import java.util.HashMap;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.progress.UIJob;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.wizard.NewSpecWizard;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.ToolboxJob;
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
        	// read UI values from the wizard page
        	final boolean importExisting = wizard.isImportExisting();
        	final String specName = wizard.getSpecName();
        	final String rootFilename = wizard.getRootFilename();
            
            // the moment the user clicks finish on the wizard page does
            // not correspond with the availability of the spec object
            // it first has to be created/parsed fully before it can be shown in
            // the editor. Thus, delay opening the editor until parsing is done.        	
            createModuleAndSpecInNonUIThread(rootFilename, importExisting, specName);
        }

        return null;
    }

	/**
     * This triggers a build which might even be blocked due to the job
     * scheduling rule, hence decouple and let the UI thread continue.
	 * @param lock 
	 */
	private void createModuleAndSpecInNonUIThread(final String rootFilename,
			final boolean importExisting, final String specName) {
		
		final Job job = new ToolboxJob("NewSpecWizard job") {
			/* (non-Javadoc)
			 * @see org.eclipse.core.runtime.jobs.Job#run(org.eclipse.core.runtime.IProgressMonitor)
			 */
			@Override
			protected IStatus run(final IProgressMonitor monitor) {
	        	// if the root file does not exist, a module has to be created
	        	final IPath rootNamePath = new Path(rootFilename);
	            if (!rootNamePath.toFile().exists())
	            {
	            	try
	            	{
	            		IWorkspaceRunnable createTLAModuleCreationOperation = ResourceHelper.createTLAModuleCreationOperation(rootNamePath);
						ResourcesPlugin.getWorkspace().run(createTLAModuleCreationOperation, monitor);
	            	} catch (final CoreException e)
	            	{
	            		final String message = "Error creating module " + rootNamePath;
	            		Activator.logError(message, e);
	            		// exception, no chance to recover
	            		return new Status(Status.ERROR, "", message, e);
	            	}
	            }
				
				// create and add spec to the spec manager
	            final Spec spec = Spec.createNewSpec(specName, rootFilename, importExisting, monitor);
				Activator.getSpecManager().addSpec(spec);
				
				// open editor since the spec has been created now
				openEditorInUIThread(spec);
				
				return Status.OK_STATUS;
			}

			/**
			 * Opens the editor for the given spec (needs access to the UI thus has to
			 * run as a UI job)
			 */
			private void openEditorInUIThread(final Spec spec) {
				// with parsing done, we are ready to open the spec editor
				final UIJob uiJob = new UIJob("NewSpecWizardEditorOpener") {
					@Override
					public IStatus runInUIThread(final IProgressMonitor monitor) {
			            // create parameters for the handler
			            final HashMap<String, String> parameters = new HashMap<String, String>();
			            parameters.put(OpenSpecHandler.PARAM_SPEC, spec.getName());

			            // runs the command
			            UIHelper.runCommand(OpenSpecHandler.COMMAND_ID, parameters);
						return Status.OK_STATUS;
					}
				};
				uiJob.schedule();
			}
		};
		job.schedule();
	}
}
