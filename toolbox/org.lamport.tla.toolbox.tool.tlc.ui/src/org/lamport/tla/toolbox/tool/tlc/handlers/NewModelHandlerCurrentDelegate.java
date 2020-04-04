package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.HashMap;
import java.util.Map;

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
            Map<String, String> parameters = new HashMap<String, String>();
            // fill the spec name for the handler
            parameters.put(NewModelHandler.PARAM_SPEC_NAME, ((Spec) current).getName());
            // delegate the call to the new model handler
            UIHelper.runCommand(NewModelHandler.COMMAND_ID, parameters);
        }
        return null;
    }
	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#isEnabled()
	 */
	@Override
	public boolean isEnabled() {
		if (ToolboxHandle.getCurrentSpec() == null) {
			return false;
		}
		return super.isEnabled();
	}
	

}
