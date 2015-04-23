package org.lamport.tla.toolbox.ui.handler;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Command handler for adding new modules (opening non-existing modules or modules in the directory of the root module)
 * 
 * @author Simon Zambrovski
 * @version $Id$
 * 
 */
public class AddModuleHandler extends AbstractHandler implements IHandler
{
    public static final String[] ACCEPTED_EXTENSIONS = { "*.tla", "*.*" };
    public static final String COMMAND_ID = "toolbox.command.module.add";

    /**
     * @see org.eclipse.core.commands.AbstractHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        IWorkbenchWindow window = HandlerUtil.getActiveWorkbenchWindowChecked(event);

        Spec spec = Activator.getSpecManager().getSpecLoaded();

        FileDialog openFileDialog = UIHelper.getFileDialog(window.getShell());
        openFileDialog.setText("Add TLA+ module to the spec");
        openFileDialog.setFilterPath(ResourceHelper.getParentDirName(spec.getRootFile()));

        openFileDialog.setFilterExtensions(ACCEPTED_EXTENSIONS);
        String moduleFileName = openFileDialog.open();
        if (moduleFileName != null)
        {
            IFile module = ResourceHelper.getLinkedFile(spec.getProject(), moduleFileName, false);

            // add .tla extension is the file does not have any extension
            if (module != null && module.getFileExtension() == null)
            {
                moduleFileName = ResourceHelper.getModuleFileName(moduleFileName);
                module = ResourceHelper.getLinkedFile(spec.getProject(), moduleFileName, false);
            }

            // check if it a TLA file
            if (!ResourceHelper.isModule(module))
            {
                // selected non-TLA file
                // module exists and is already registered in the spec
                MessageDialog.openInformation(window.getShell(), "The selected file is not a TLA+ file",
                        "The provided file " + module.getName()
                                + " is not a TLA+ file.\n Please select a file with .tla extension.");
                return null;

            } else
            {
                if (module.isLinked())
                {
                    // module exists and is already registered in the spec
                    MessageDialog.openInformation(window.getShell(), "TLA+ Module is part of the spec",
                            "The provided module " + module.getName()
                                    + " has already been added to the specification previously.");
                } else
                {
                    IPath modulePath = new Path(moduleFileName);
                    // check the folder we are in
                    if (!ResourceHelper.isProjectParent(modulePath.removeLastSegments(1), spec.getProject()))
                    {
                        // the selected resource is not in the same directory as the root file
                        MessageDialog
                                .openInformation(
                                        window.getShell(),
                                        "Wrong TLA+ Module is part of the spec",
                                        "The provided module "
                                                + module.getName()
                                                + " is not located in the same directory as the root file. \nPlease select the module in "
                                                + spec.getRootFile().getFullPath().removeLastSegments(1).toOSString());
                        return null;
                    }

                    // !module.exists()
                    if (!modulePath.toFile().exists())
                    {
                        // the provided file does not exist
                        boolean createNew = MessageDialog.openQuestion(window.getShell(), "TLA+ Module is not found",
                                "The provided module " + module.getName()
                                        + " does not exist. Should the new file be created?");
                        if (createNew)
                        {
                            // the module point to a virtual path /WS_ROOT/SPEC_NAME/module_name.tla
                            // assuming the fact that the root file is located in directory /ROOT_DIR/SPEC_NAME.tla
                            // and the Spec's project name is /ROOT_DIR/SPEC_NAME.project
                            // the file should be created in /ROOT_DIR/module_name.tla and linked to the virtual path.

                            try
                            {
                                ResourcesPlugin.getWorkspace().run(
                                        ResourceHelper.createTLAModuleCreationOperation(modulePath), null);
                            } catch (CoreException e)
                            {
                                e.printStackTrace();
                                // exception, no chance to recover
                                return null;
                            }
                        } else
                        {
                            return null;
                        }
                    }
                    // adding the file to the spec
					module = createModuleFile(spec, moduleFileName, modulePath);
                }

                // create parameters for the handler
                Map<String, String> parameters = new HashMap<String, String>();
                parameters.put(OpenModuleHandler.PARAM_MODULE, ResourceHelper.getModuleNameChecked(module.getName(),
                        false));

                // runs the command and opens the module in the editor
                UIHelper.runCommand(OpenModuleHandler.COMMAND_ID, parameters);
            }
        }

        return null;
    }

	public IFile createModuleFile(final Spec spec, String moduleFileName, final IPath modulePath) {
		// Convert the OS specific absolute path to an Eclipse
		// specific relative one that is portable iff the resource
		// is in the project's folder hierarchy.
		// Technically this will always evaluate to true. One of the
		// checks above makes sure that one can only add modules
		// residing in the project's parent.
		if (ResourceHelper.isProjectParent(modulePath.removeLastSegments(1), spec.getProject())) {
			moduleFileName = ResourceHelper.PARENT_ONE_PROJECT_LOC + modulePath.lastSegment();
		}
		// adding the file to the spec
		return ResourceHelper.getLinkedFile(spec.getProject(), moduleFileName, true);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#isEnabled()
	 */
	@Override
	public boolean isEnabled() {
		if (Activator.getSpecManager().getSpecLoaded() == null) {
			return false;
		}
		return super.isEnabled();
	}
}
