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
 Switches perspective
 *    <code>
 *      <command
 *           categoryId="toolbox.command.category.ui"
 *           description="Switches to the perspective"
 *           id="toolbox.command.switchperspective"
 *           name="Switches to the perspective">
 *        <commandParameter
 *              id="toolbox.switchperspective.id"
 *              name="name"
 *              optional="false">
 *        </commandParameter>
 *     </command>
 *     <menuContribution
 *           locationURI="menu:toolbox.window.menu?after=toolbox.window.tools.separator">
 *        <command
 *              commandId="toolbox.command.switchperspective"
 *              id="toolbox.menu.switchperspective-specLoaded"
 *              label="Specification"
 *              mode="FORCE_TEXT"
 *              style="radio">
 *           <parameter
 *                 name="toolbox.switchperspective.id"
 *                 value="org.lamport.tla.toolbox.ui.perspective.specLoaded">
 *           </parameter>
 *        </command>
 *     </menuContribution>
 * </code>
 * @author Simon Zambrovski
 * @version $Id$ 
 * @deprecated Simon says it is not used now.
 */
public class SwitchPerspectiveHandler extends AbstractHandler implements IHandler, IElementUpdater
{
    public static final String COMMAND_ID = "toolbox.command.switchperspective";
    public static final String PARAM_PERSPECTIVE_ID = "toolbox.switchperspective.id";

    public Object execute(final ExecutionEvent event) throws ExecutionException
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

        final ICommandService service = (ICommandService) HandlerUtil.getActiveWorkbenchWindowChecked(event).getService(
                ICommandService.class);

        /**
         * opens a perspective by name
         */
        UIHelper.runUIAsync(new Runnable() {
            public void run()
            {
                UIHelper.switchPerspective(perspectiveId);

                // update our radio button states ... get the service from
                // a place that's most appropriate
                // but do it in the same thread, and AFTER the UI has been updated
                service.refreshElements(event.getCommand().getId(), null);
            }
        });


        return null;
    }

    public void updateElement(UIElement element, Map parameters)
    {
        String parameter = (String) parameters.get(PARAM_PERSPECTIVE_ID);
        if (parameter != null)
        {
            if (UIHelper.getActivePerspectiveId().equals(parameter))
            {
                element.setChecked(true);
            } else
            {
                element.setChecked(false);
            }
        }
    }

}
