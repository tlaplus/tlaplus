package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.ui.perspective.ProblemsPerspective;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
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
        /**
         * toggle means if it shown hide it if it is hidden, show it
         */
        UIHelper.runUIAsync(new Runnable() {
            public void run()
            {
                
                if (UIHelper.isPerspectiveShown(ProblemsPerspective.ID))
                {
                    // the problem view is shown
                    UIHelper.closeWindow(ProblemsPerspective.ID);
                } else {
                    // the problem view is hidden, show it if problems are in place
                    // if (AdapterFactory.isProblemStatus(spec.getStatus()))
                    if (TLAMarkerHelper.currentSpecHasProblems())
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
