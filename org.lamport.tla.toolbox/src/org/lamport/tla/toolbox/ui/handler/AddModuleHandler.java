package org.lamport.tla.toolbox.ui.handler;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.HashMap;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.SWT;
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

        FileDialog openFileDialog = new FileDialog(window.getShell(), SWT.OPEN);
        openFileDialog.setText("Add TLA+ module to the spec");
        openFileDialog.setFilterPath(spec.getRootFile().getLocation().toOSString());

        openFileDialog.setFilterExtensions(ACCEPTED_EXTENSIONS);
        final String moduleFileName = openFileDialog.open();
        if (moduleFileName != null)
        {
            
            
            // TODO check the folder we are in
            
            // TODO check if it a TLA file
            
            
            
            IFile module = ResourceHelper.getLinkedFile(spec.getProject(), moduleFileName, false);
            if (module.isLinked())
            {
                // module exists and is already registered in the spec
                MessageDialog.openInformation(window.getShell(), "TLA+ Module is part of the spec",
                        "The provided module " + module.getName()
                                + " has already been added to the specification previously.");
            } else
            {
                if (!module.exists())
                {
                    // the provided file does mnot exist
                    boolean createNew = MessageDialog.openQuestion(window.getShell(), "TLA+ Module is not found",
                            "The provided module " + module.getName()
                                    + " does not exist. Should the new file be created?");
                    if (createNew) 
                    {
                        // the module point to a virtual path /WS_ROOT/SPEC_NAME/module_name.tla
                        // assuming the fact that the root file is located in directory /ROOT_DIR/SPEC_NAME.tla
                        // and the Spec's project name is /ROOT_DIR/SPEC_NAME.project
                        // the file should be created in /ROOT_DIR/module_name.tla and linked to the virtual path.

                        IWorkspaceRunnable moduleCreateOperation = new TLAModuleCreationOperation(new Path(moduleFileName));
                        
                        try
                        {
                            ResourcesPlugin.getWorkspace().run(moduleCreateOperation, null);
                        } catch (CoreException e)
                        {
                            e.printStackTrace();
                            // exception, no chance to recover
                            return null;
                        }
                    } else {
                        return null;
                    }
                }
                // adding the file to the spec
                module = ResourceHelper.getLinkedFile(spec.getProject(), moduleFileName, true);
            }

            // create parameters for the handler
            HashMap parameters = new HashMap();
            parameters
                    .put(OpenModuleHandler.PARAM_MODULE, ResourceHelper.getModuleNameChecked(module.getName(), false));

            // runs the command
            UIHelper.runCommand(OpenModuleHandler.COMMAND_ID, parameters);
        }

        return null;
    }
    

    /**
     * Operation for creation of the new TLA+ module with default content
     * @author Simon Zambrovski
     * @version $Id$
     */
    class TLAModuleCreationOperation implements IWorkspaceRunnable
    {
        private IPath modulePath;

        /**
         * constructs the creation operation
         * @param module REAL module path to be created
         */
        public TLAModuleCreationOperation(IPath module)
        {
            this.modulePath = module;
            
        }
        public void run(IProgressMonitor monitor)
        {
            String moduleFileName = modulePath.lastSegment();
            
            byte[] content = ResourceHelper.getModuleDefaultContent(moduleFileName);
            try
            {
                // create file
                File file = new File(modulePath.toOSString());
                if (file.createNewFile())
                {
                    //successfully created
                    FileOutputStream fos = new FileOutputStream(file);
                    fos.write(content);
                    fos.flush();
                    fos.close();
                } else {
                    throw new RuntimeException("Error creating a file");
                }
            } catch (IOException e)
            {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
            
        }
        
    }
}
