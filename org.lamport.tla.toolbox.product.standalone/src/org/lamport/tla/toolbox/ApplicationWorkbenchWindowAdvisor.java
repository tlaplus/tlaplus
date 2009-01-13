package org.lamport.tla.toolbox;

import org.eclipse.swt.graphics.Point;
import org.eclipse.ui.application.ActionBarAdvisor;
import org.eclipse.ui.application.IActionBarConfigurer;
import org.eclipse.ui.application.IWorkbenchWindowConfigurer;
import org.eclipse.ui.application.WorkbenchWindowAdvisor;

/**
 * Configuration of the main window
 *
 * @author zambrovski
 */
public class ApplicationWorkbenchWindowAdvisor extends WorkbenchWindowAdvisor
{

    public ApplicationWorkbenchWindowAdvisor(IWorkbenchWindowConfigurer configurer)
    {
        super(configurer);
    }

    public ActionBarAdvisor createActionBarAdvisor(IActionBarConfigurer configurer)
    {
        return new ApplicationActionBarAdvisor(configurer);
    }

    public void preWindowOpen()
    {
        IWorkbenchWindowConfigurer configurer = getWindowConfigurer();
        configurer.setInitialSize(new Point(800, 600));
        configurer.setShowStatusLine(true);
        configurer.setShowCoolBar(false);
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.application.WorkbenchWindowAdvisor#postWindowOpen()
     */
    public void postWindowOpen()
    {
        super.postWindowOpen();
        // check if this is really required
        // UIHelper.switchPerspective(InitialPerspective.ID);
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.application.WorkbenchWindowAdvisor#preWindowShellClose()
     */
    public boolean preWindowShellClose()
    {
        //
        // save the editors?
        /*
        Spec spec = Activator.getSpecManager().getSpecLoaded();
        if (spec != null) 
        {
            spec.setOpenedModules(UIHelper.getOpenedResources());
        }
        */
        return super.preWindowShellClose();
    }

    
    
}
