package org.lamport.tla.toolbox.ui.handler;

import java.util.Map;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.commands.IElementUpdater;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.menus.UIElement;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Switches perspective
 * @author Simon Zambrovski
 * @version $Id$ 
 */
public class SwichPerspectiveHandler extends AbstractHandler implements IHandler, IElementUpdater
{
    public static final String COMMAND_ID = "toolbox.command.switchperspective";
    public static final String PARAM_PERSPECTIVE_ID = "toolbox.switchperspective.id";

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        final String perspectiveId = event.getParameter(PARAM_PERSPECTIVE_ID);
        if (perspectiveId == null)
        {
            return null;
        }

        // in theory, we're already in the correct state
        if (UIHelper.getActivePerspectiveId().equals(perspectiveId))
        {
            return null;
        }

        /**
         * opens a perspective by name
         */
        UIHelper.runUIAsync(new Runnable() {
            public void run()
            {
                UIHelper.switchPerspective(perspectiveId);
            }
        });

        // update our radio button states ... get the service from
        // a place that's most appropriate
        ICommandService service = (ICommandService) HandlerUtil.getActiveWorkbenchWindowChecked(event).getService(
                ICommandService.class);
        service.refreshElements(event.getCommand().getId(), null);

        return null;
    }

    public void updateElement(UIElement element, Map parameters)
    {
        String parm = (String) parameters.get(PARAM_PERSPECTIVE_ID);
        if (parm != null)
        {
            if (UIHelper.getActivePerspectiveId().equals(parm))
            {
                element.setChecked(true);
            } else
            {
                element.setChecked(false);
            }
        }
    }

}
