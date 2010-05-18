package org.lamport.tla.toolbox.tool.tlc.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.editor.basic.TLAEditorReadOnly;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Opens a module in a read-only editor. This handler has one required
 * parameter, the String representing the full file system path to the
 * module to be opened. This String should be created using {@link Path#toPortableString()}.
 * 
 * @author Daniel Ricketts
 *
 */
public class OpenSavedModuleHandler extends AbstractHandler implements IHandler
{

    public static final String COMMAND_ID = "toolbox.tool.tlc.commands.open.savedModule";
    /**
     * String parameter giving the full file system path to the module to be opened.
     * This String should have been created using {@link Path#toPortableString()}.
     */
    public static final String PARAM_MODULE_PATH = "toolbox.tool.tlc.commands.open.savedModule.modulePath";

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        String pathString = event.getParameter(PARAM_MODULE_PATH);
        if (pathString != null)
        {
            /*
             * Try to get the module from the path passed in as a parameter.
             */
            IPath modulePath = Path.fromPortableString(pathString);
            IFile module = ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(modulePath);
            if (module != null && module.exists())
            {
                /*
                 * Check to see if the module is part of the currently opened
                 * spec. The project containing the module is the project of the
                 * spec of the module. If this is not equal to the project of the
                 * currently opened spec, it is a bug.
                 */
                if (module.getProject().equals(ToolboxHandle.getCurrentSpec().getProject()))
                {
                    /*
                     * The parent of the module is the model folder, so it is the name
                     * of the model.
                     */
                    ILaunchConfiguration config = ModelHelper.getModelByName(module.getProject(), module.getParent()
                            .getName());
                    ModelEditor modelEditor = (ModelEditor) UIHelper.openEditor(ModelEditor.ID, config.getFile());
                    if (modelEditor != null)
                    {
                        try
                        {
                            /*
                             * First, we determine if the model editor already has the
                             * saved module open in an editor. If it does, activate
                             * that page. If it doesn't, add a new page with an read-only
                             * editor open on the module.
                             * 
                             * The only method to get currently opened editors in the model
                             * editor is findEditors(editorInput) which returns an array
                             * of currently opened editors on the input. This should only
                             * have length one, but for whatever reason we may decide in
                             * the future to have more than one editor open on a given input.
                             * If there is more than one open, just activate the first one
                             * in the returned array.
                             */
                            FileEditorInput editorInput = new FileEditorInput(module);
                            IEditorPart[] editors = modelEditor.findEditors(editorInput);
                            IEditorPart moduleEditor = null;
                            if (editors.length > 0)
                            {
                                moduleEditor = editors[0];
                            } else
                            {
                                moduleEditor = new TLAEditorReadOnly();
                                modelEditor.addPage(moduleEditor, editorInput);
                            }

                            modelEditor.setActiveEditor(moduleEditor);
                        } catch (PartInitException e)
                        {
                            TLCUIActivator.logError("Error adding saved module read-only editor for module "
                                    + modulePath + " to model " + config.getName(), e);
                        }
                    } else
                    {
                        TLCUIActivator.logDebug("Could not open model editor for model " + config.getName());
                    }
                } else
                {
                    TLCUIActivator
                            .logDebug("OpenSavedModuleHandler was passed a module file path that is not part of the currently opened spec."
                                    + "This is a bug. The path is " + modulePath);
                }
            }
        }
        return null;
    }
}
