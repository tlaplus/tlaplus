package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IFile;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPropertyListener;
import org.eclipse.ui.IWorkbenchPartConstants;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Handles the open-module command
 * @author Simon Zambrovski
 * @version $Id: OpenSpecHandler.java 155 2009-01-29 05:11:44Z simonzam $
 */
public class OpenModuleHandler extends AbstractHandler implements IHandler
{
    public static final String COMMAND_ID = "toolbox.command.module.open";
    public static final String PARAM_MODULE = "toolbox.command.module.open.param";

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        String moduleName = event.getParameter(PARAM_MODULE);
        if (moduleName == null)
        {
            throw new RuntimeException("Module was null" );
        }

        final IFile module = ResourceHelper.getLinkedFile(Activator.getSpecManager().getSpecLoaded().getProject(), ResourceHelper.getModuleFileName(moduleName));
        if (module == null)
        {
            // TODO return some error
            throw new RuntimeException("Module " + moduleName + " could not be found" );
            // return null;
        }

        // open the editor
        IEditorPart part = UIHelper.openEditor(OpenSpecHandler.TLA_EDITOR, new FileEditorInput(module));
        part.addPropertyListener(new IPropertyListener() {

            public void propertyChanged(Object source, int propId)
            {
                if (IWorkbenchPartConstants.PROP_DIRTY == propId)
                {
                    // here the listeners to editor changes go into
                    
                } 
            }
        });

        return null;
    }

}
