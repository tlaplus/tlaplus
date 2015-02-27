package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.ui.navigator.ToolboxExplorer;
import org.lamport.tla.toolbox.ui.perspective.InitialPerspective;
import org.lamport.tla.toolbox.ui.view.ProblemView;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Closes the specification and switches the UI back to the initial perspective
 *
 * @author zambrovski
 */
public class CloseSpecHandler extends AbstractHandler implements IHandler
{
    public final static String COMMAND_ID = "toolbox.command.spec.close";
    
    // A QualifiedName for the project's last closed time persistent property.
    public static final QualifiedName LAST_CLOSED_DATE = 
        new QualifiedName(COMMAND_ID, "lastClosedTime");

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        // Set the project's last closed time to the current time.
        try
        {
            Activator.getSpecManager().getSpecLoaded().getProject().setPersistentProperty(
               LAST_CLOSED_DATE, "" + System.currentTimeMillis());
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            Activator.getDefault().logDebug(
             "Exception thrown when setting project LAST_CLOSED time.");
        }
        // close all editors
        UIHelper.getActivePage().closeAllEditors(true);
        // hide errors
        UIHelper.hideView(ProblemView.ID);
        // switch perspective
        UIHelper.switchPerspective(InitialPerspective.ID);
        
        // Refresh the CommonViewer to causes it to align the icon shown in the SpecExplorer
        // with the state of the spec. E.g. if the spec is closed, make sure it shows the closed
        // project icon.
        final WorkspaceSpecManager specManager = Activator.getSpecManager();
        final ToolboxExplorer toolboxExplorer = (ToolboxExplorer) UIHelper.findView(ToolboxExplorer.VIEW_ID);
        if (toolboxExplorer != null) {
			final Spec specClosed = specManager.getSpecLoaded();
			toolboxExplorer.getCommonViewer().refresh(specClosed);
        }

        // unset the spec
        specManager.setSpecLoaded(null);
        return null;
    }

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#isEnabled()
	 */
//	@Override
//	public boolean isEnabled() {
//		if (Activator.getSpecManager().getSpecLoaded() == null) {
//			return false;
//		}
//		return super.isEnabled();
//	}

}
