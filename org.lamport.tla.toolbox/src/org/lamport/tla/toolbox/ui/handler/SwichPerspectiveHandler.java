package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Switches perspective
 * @author Simon Zambrovski
 * @version $Id$ 
 */
public class SwichPerspectiveHandler extends AbstractHandler implements IHandler
{

    private static final String PARAM_PERSPECTIVE_ID = "toolbox.switchperspective.id";

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        
        final String perspectiveId = event.getParameter(PARAM_PERSPECTIVE_ID);
        if (perspectiveId == null)
        {
            return null;
        }
        /**
         * opens a view by name
         */
        UIHelper.runUIAsync(new Runnable() 
        {
            public void run()
            {
                UIHelper.switchPerspective(perspectiveId);
            }
        });

        return null;
    }

}
