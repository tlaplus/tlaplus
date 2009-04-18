package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Opens the view specified by name as parameter
 * @author Simon Zambrovski
 * @version $Id$
 */
public class OpenViewHandler extends AbstractHandler implements IHandler
{

    private static final String PARAM_VIEW_NAME = "toolbox.openview.name";

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        
        final String viewName = event.getParameter(PARAM_VIEW_NAME);
        if (viewName == null)
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
                UIHelper.openView(viewName);
            }
        });

        return null;
    }

}
