package org.lamport.tla.toolbox;

import org.eclipse.swt.graphics.Point;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.application.ActionBarAdvisor;
import org.eclipse.ui.application.IActionBarConfigurer;
import org.eclipse.ui.application.IWorkbenchWindowConfigurer;
import org.eclipse.ui.application.WorkbenchWindowAdvisor;

/**
 * Configuration of the main window
 * @version $Id$
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
        configurer.setShowFastViewBars(true);
        configurer.setShowStatusLine(true);
        configurer.setShowProgressIndicator(true);
        configurer.setShowCoolBar(false);
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.application.WorkbenchWindowAdvisor#preWindowShellClose()
     */
    public boolean preWindowShellClose()
    {

        IWorkbench workbench = getWindowConfigurer().getWorkbenchConfigurer().getWorkbench();
        /*
         * if more than one window is opened and currently the root window is being closed, exit the application
         */
        if (workbench.getWorkbenchWindowCount() > 1 && WindowUtils.isRootWindow(workbench.getActiveWorkbenchWindow()))
        {
            // System.out.println("A root shell is about to be closed");
            return workbench.close();
        } else
        {
            return super.preWindowShellClose();
        }
    }

}
