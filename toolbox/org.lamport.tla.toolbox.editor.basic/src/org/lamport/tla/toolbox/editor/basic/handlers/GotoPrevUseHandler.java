/**
 * 
 */
package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IMarker;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;

/**
 * @author lamport
 *
 */
public class GotoPrevUseHandler extends AbstractHandler implements IHandler
{

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        Spec spec = ToolboxHandle.getCurrentSpec();
        if (spec == null)
        {
            // This should not happen.
            return null;
        }
        IMarker[] markers = spec.getMarkersToShow();
        if (markers == null)
        {
            // This should not happen.
            return null;
        }
        int selection = spec.getCurrentSelection();
        if (selection == 0) {
            selection = markers.length - 1;
        } else {
            selection = selection - 1;
        }
        spec.setCurrentSelection(selection);
        GotoNextUseHandler.jumpToCurrentSelection(spec);

        return null;
    }
    
    public boolean isEnabled()
    {
        Spec spec = ToolboxHandle.getCurrentSpec();
        if (spec == null)
        {
            return false;
        }
        return spec.getMarkersToShow() != null;
    }

}
