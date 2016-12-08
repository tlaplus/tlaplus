package org.lamport.tla.toolbox.ui.handler;

import java.util.HashMap;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
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
import org.lamport.tla.toolbox.ui.navigator.ToolboxExplorer;
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
	public static final String PARAM_PATH = "toolbox.command.spec.new.param";

    /**
     * @see org.eclipse.core.commands.AbstractHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        IWorkbenchWindow window = HandlerUtil.getActiveWorkbenchWindowChecked(event);

        // Create the wizard
        NewSpecWizard wizard = new NewSpecWizard(event.getParameter(PARAM_PATH));
        // we pass null for structured selection, cause we just not using it
        wizard.init(window.getWorkbench(), null);
        Shell parentShell = window.getShell();
        // Create the wizard dialog
        WizardDialog dialog = new WizardDialog(parentShell, wizard);
        dialog.setHelpAvailable(true);
        
        // Open the wizard dialog
        if (Window.OK == dialog.open() && wizard.getRootFilename() != null)
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
		Assert.isNotNull(rootFilename);
		Assert.isNotNull(specName);
		
		final Job job = new NewSpecHandlerJob(specName, rootFilename, importExisting);
		job.schedule();
	}
	
	public static class NewSpecHandlerJob extends ToolboxJob {

		private final String specName;
		private final String rootFilename;
		private final boolean importExisting;

		public NewSpecHandlerJob(String specName, String rootFilename, boolean importExisting) {
			super("NewSpecWizard job");
			this.specName = specName;
			this.rootFilename = rootFilename;
			this.importExisting = importExisting;
		}

		@Override
		protected IStatus run(IProgressMonitor monitor) {
			final IProject project = ResourceHelper.getProject(specName);
			if (project.exists() && Activator.getSpecManager().getSpecByName(specName) == null) {
				// There exists a project by that name already without
				// a corresponding spec instance. This is most likely
				// the result of an earlier delete that went south. Ask the user
				// if the project should be deleted.
				Activator.getSpecManager().addSpec(new Spec(project, project.getFile("Delete me")));
				UIHelper.runUIAsync(new Runnable() {
					public void run() {
						// This refresh should not be necessary when the
						// ToolboxExplorer would correctly listen for the spec
						// created event fired by the spec manager.
						ToolboxExplorer.refresh();
					}
				});
				return new Status(Status.ERROR, "org.lamport.tla.toolbox",
						String.format(
								"The workspace already contains a spec by the name '%1$s' located at '%2$s'. "
										+ "Please delete the spec '%1$s [ %3$s ]' from the Spec Explorer. "
										+ "Afterwards, try to create your new spec again.\n"
										+ "If there is no spec '%1$s [ %3$s ]' in the Spec Explorer, then "
										+ "this is a bug. Please file a bug report and choose a different "
										+ "specification name when you create a new spec in the meantime.",
								specName, project.getLocation().toOSString(), "Delete me"));
			}
			
			// if the root file does not exist, a module has to be created
			final IPath rootNamePath = new Path(rootFilename);
			try {
				if (!rootNamePath.toFile().exists()) {
					IWorkspaceRunnable createTLAModuleCreationOperation = ResourceHelper
							.createTLAModuleCreationOperation(rootNamePath);
					ResourcesPlugin.getWorkspace().run(createTLAModuleCreationOperation, monitor);
				}
				
				// create and add spec to the spec manager
				final Spec spec = Spec.createNewSpec(specName, rootFilename, importExisting, monitor);
				Activator.getSpecManager().addSpec(spec);

				// open editor since the spec has been created now
				openEditorInUIThread(spec);
			} catch (final CoreException e) {
				final String message = "Error creating module " + rootNamePath;
				Activator.getDefault().logError(message, e);
				// exception, no chance to recover
				return new Status(Status.ERROR, "org.lamport.tla.toolbox", message, e);
			}

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
	}
}
