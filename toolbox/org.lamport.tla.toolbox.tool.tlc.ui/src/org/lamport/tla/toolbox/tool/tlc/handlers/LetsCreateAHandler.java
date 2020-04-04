package org.lamport.tla.toolbox.tool.tlc.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;

/**
 * TODO LL says he deletes this file as soon as he does not need it anymore
 * @author Leslie Lamport
 *
 */
public class LetsCreateAHandler extends AbstractHandler
{

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        return null;
    }
    
// I thought the following should make the menu item invisible, but 
// it at first seemed to be random.  Sometimes it did nothing, and then when
// I select another view it grayed it out.  Sometimes the menu item
// was invisible when I open the toolbox.  It seems now to have stabilized
// to the latter behavior.
//    
    public boolean isEnabled() {
        return false;
    }
}
