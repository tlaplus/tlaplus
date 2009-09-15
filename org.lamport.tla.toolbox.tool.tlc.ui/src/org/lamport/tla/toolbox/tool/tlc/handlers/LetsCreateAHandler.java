package org.lamport.tla.toolbox.tool.tlc.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;

public class LetsCreateAHandler extends AbstractHandler
{

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
System.out.println("Let's create a command class handler blah.");
       // TODO Auto-generated method stub
        return null;
    }
    
// I thought the following should make the menu item invisible, but 
// it at first seemed to be random.  Sometimes it did nothing, and then when
// I select another view it grayed it out.  Sometimes the menu item
// was invisible when I open the toolbox.  It seems now to have stabilized
// to the latter behavior.
//    
    public boolean isEnabled() {
//        super.setEnabled(this); 
        return false;
    }
}
