package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.perspective.ProblemsPerspective;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Toggles the problem view (hides if it shown, shows if it is hidden)
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ToggleProblemViewHandler extends AbstractHandler implements IHandler
{

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        UIHelper.runUIAsync(new Runnable() {
            public void run()
            {
                
                if (UIHelper.isPerspectiveShown(ProblemsPerspective.ID))
                {
                    // the problem view is shown
                    UIHelper.closeWindow(ProblemsPerspective.ID);
                } else {
                    // the problem view is hidden
                    Spec spec = Activator.getSpecManager().getSpecLoaded();
                    if (AdapterFactory.isProblemStatus(spec.getStatus()))
                    {
                        UIHelper.openPerspectiveInWindowRight(ProblemsPerspective.ID, null,
                                ProblemsPerspective.WIDTH);
                    }
                }
            }
        });

        return null;
    }

}
