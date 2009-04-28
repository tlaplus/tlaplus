package org.lamport.tla.toolbox;

import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.ui.application.IWorkbenchConfigurer;
import org.eclipse.ui.application.IWorkbenchWindowConfigurer;
import org.eclipse.ui.application.WorkbenchAdvisor;
import org.eclipse.ui.application.WorkbenchWindowAdvisor;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.UIHelper;
import org.eclipse.ui.internal.ide.model.WorkbenchAdapterBuilder;

/**
 * This workbench advisor creates the window advisor, and specifies
 * the perspective id for the initial window.
 * @author Simon Zambrovski
 * @version $Id$ 
 */
public class ApplicationWorkbenchAdvisor extends WorkbenchAdvisor
{

    public static final String PERSPECTIVE_ID = "org.lamport.tla.toolbox.ui.perspective.initial";

    public WorkbenchWindowAdvisor createWorkbenchWindowAdvisor(IWorkbenchWindowConfigurer configurer)
    {
        return new ApplicationWorkbenchWindowAdvisor(configurer);
    }

    public String getInitialWindowPerspectiveId()
    {
        return PERSPECTIVE_ID;
    }

    public IAdaptable getDefaultPageInput()
    {
        IWorkspace workspace = ResourcesPlugin.getWorkspace();
        return workspace.getRoot();
    }

    /*
     * @see org.eclipse.ui.application.WorkbenchAdvisor#initialize(org.eclipse.ui.application.IWorkbenchConfigurer)
     */
    public void initialize(IWorkbenchConfigurer configurer)
    {

        super.initialize(configurer);
        // save the positions of windows etc...
        configurer.setSaveAndRestore(true);

        // register adapter
        WorkbenchAdapterBuilder.registerAdapters();

    }

    public boolean preShutdown()
    {
        if (!ToolboxHandle.getInstanceStore().getBoolean(ToolboxHandle.I_RESTORE_LAST_SPEC))
        {
            UIHelper.getActivePage().closeAllEditors(true);
            UIHelper.switchPerspective(getInitialWindowPerspectiveId());
        }
        return super.preShutdown();
    }
}
