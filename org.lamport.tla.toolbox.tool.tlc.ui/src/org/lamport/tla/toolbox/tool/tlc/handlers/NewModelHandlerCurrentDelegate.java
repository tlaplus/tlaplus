package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.HashMap;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Delegates the model creation for the currently selected spec
 * @author Simon Zambrovski
 * @version $Id$
 */
public class NewModelHandlerCurrentDelegate extends AbstractHandler implements IHandler
{
    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        // get the current spec
        Spec current = ToolboxHandle.getCurrentSpec();
        if (current != null)
        {
            HashMap parameters = new HashMap();
            // fill the spec name for the handler
            parameters.put(NewModelHandler.PARAM_SPEC_NAME, ((Spec) current).getName());
            // delegate the call to the new model handler
            UIHelper.runCommand(NewModelHandler.COMMAND_ID, parameters);
        }
        return null;
    }

}
