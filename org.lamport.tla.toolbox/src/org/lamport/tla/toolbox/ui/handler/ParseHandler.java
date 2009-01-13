package org.lamport.tla.toolbox.ui.handler;

import java.util.List;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.IParserLauncher;
import org.lamport.tla.toolbox.spec.parser.StreamInterpretingParserLauncher;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Triggers parsing of specification's root file
 * 
 * @author zambrovski
 */
public class ParseHandler extends AbstractHandler implements IHandler
{

    IParserLauncher launcher = new StreamInterpretingParserLauncher();

    /*
     * non-JavaDoc
     * @see IHandler#execute(ExecutionEvent event)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        List references = UIHelper.checkOpenResources("Modified resources", "Some resources are modified.\nDo you want to save the modified resources?");
        for (int i =0; i < references.size(); i++) 
        {
            // save resources
            // ((EditorReference)references.get(i)).getEditor(false);
        }
        Spec spec = Activator.getSpecManager().getSpecLoaded();

        if (spec != null)
        {
            int status = launcher.parseSpecification(spec);

            Activator.getParserRegistry().parseResultChanged(status);

        } else
        {
            // TODO handle this case (could it occur?, declare in plugin.xml to activate the parse button on active
            // editor only)
        }
        return null;
    }

}
