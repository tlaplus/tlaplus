package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.perspective.InitialPerspective;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Closes the specification and switches the UI back to the initial perspective
 *
 * @author zambrovski
 */
public class CloseSpecHandler extends AbstractHandler implements IHandler
{

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        Spec currentSpec =  Activator.getSpecManager().getSpecLoaded();
        
        String[] openedResources = UIHelper.getOpenedResources();
        if (currentSpec != null) 
        {
            currentSpec.setOpenedModules(openedResources);
        }
        UIHelper.getActivePage().closeAllEditors(true);
        UIHelper.switchPerspective(InitialPerspective.ID);
        Activator.getSpecManager().setSpecLoaded(null);
        return null;
    }

}
