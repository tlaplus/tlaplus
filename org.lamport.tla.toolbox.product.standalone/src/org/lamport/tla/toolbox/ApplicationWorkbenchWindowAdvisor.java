package org.lamport.tla.toolbox;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.eclipse.jface.preference.IPreferenceNode;
import org.eclipse.jface.preference.PreferenceManager;
import org.eclipse.swt.graphics.Point;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PlatformUI;
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

	/* (non-Javadoc)
	 * @see org.eclipse.ui.application.WorkbenchWindowAdvisor#postWindowOpen()
	 */
	public void postWindowOpen() {
		final PreferenceManager preferenceManager = PlatformUI.getWorkbench().getPreferenceManager();
		
		// @see http://bugzilla.tlaplus.net/show_bug.cgi?id=191
		final List filters = new ArrayList();
		filters.add("org.eclipse.compare.internal.ComparePreferencePage");
		
		// Clean the preferences
		final List elements = preferenceManager.getElements(PreferenceManager.POST_ORDER);
		for (Iterator iterator = elements.iterator(); iterator.hasNext();) {
			final Object elem = (Object) iterator.next();
			if (elem instanceof IPreferenceNode) {
				if (filters.contains(((IPreferenceNode) elem).getId())) {
					preferenceManager.remove((IPreferenceNode) elem);
				}
			}
		}

		super.postWindowOpen();
	}
	
}
