package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IFile;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.perspective.InitialPerspective;
import org.lamport.tla.toolbox.ui.perspective.SpecLoadedPerspective;
import org.lamport.tla.toolbox.util.PreferenceStoreHelper;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

public class OpenSpecHandler extends AbstractHandler implements IHandler
{
    public static final String TLA_EDITOR = "org.lamport.tla.toolbox.editor.basic.TLAEditor";
    public static final String COMMAND_ID = "toolbox.command.openSpec";
    public static final String PARAM_SPEC = "toolbox.command.openSpec.param";

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        String specName = event.getParameter(PARAM_SPEC);
        if (specName == null)
        {
            return null;
        }

        Spec spec = Activator.getSpecManager().getSpecByName(specName);
        if (spec == null)
        {
            return null;
        }

        // spec the perspective
        UIHelper.switchPerspective(SpecLoadedPerspective.ID);
        // close the initial perspective
        UIHelper.closeWindow(InitialPerspective.ID);
       

        String[] editors = PreferenceStoreHelper.getOpenedEditors(spec.getProject());
        if (editors.length != 0)
        {

            for (int i = 0; i < editors.length; i++)
            {
                // IEditorInput input = new FileEditorInput(this.spec.getRootFile());

                IFile file = ResourceHelper.getLinkedFile(spec.getProject(), editors[i]);

                // open the editor
                UIHelper.openEditor(TLA_EDITOR, new FileEditorInput(file));

            }
        } else
        {
            // open the editor
            UIHelper.openEditor(TLA_EDITOR, new FileEditorInput(spec.getRootFile()));
        }



        // store information about opened spec in the spec manager
        Activator.getSpecManager().setSpecLoaded(spec);
        
        return null;
    }

}
