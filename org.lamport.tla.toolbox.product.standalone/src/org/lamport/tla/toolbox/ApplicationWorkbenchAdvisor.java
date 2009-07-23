package org.lamport.tla.toolbox;

import java.net.URL;

import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.application.IWorkbenchConfigurer;
import org.eclipse.ui.application.IWorkbenchWindowConfigurer;
import org.eclipse.ui.application.WorkbenchAdvisor;
import org.eclipse.ui.application.WorkbenchWindowAdvisor;
import org.eclipse.ui.ide.IDE;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.ToolboxLifecycleException;
import org.lamport.tla.toolbox.tool.ToolboxLifecycleParticipant;
import org.lamport.tla.toolbox.util.ToolboxParticipantManger;
import org.lamport.tla.toolbox.util.UIHelper;
import org.osgi.framework.Bundle;

/**
 * This workbench advisor creates the window advisor, and specifies
 * the perspective id for the initial window.
 * @author Simon Zambrovski
 * @version $Id$ 
 */
public class ApplicationWorkbenchAdvisor extends WorkbenchAdvisor
{

    // TODO MOVE!
    public static final String PERSPECTIVE_ID = "org.lamport.tla.toolbox.ui.perspective.initial";
    public static final String IDE_PLUGIN = "org.eclipse.ui.ide";
    public static final String PATH_OBJECT = "icons/full/obj16/";
    public static final String PATH_WIZBAN = "icons/full/wizban/";
    
    public static final String PRJ_OBJ = PATH_OBJECT + "prj_obj.gif"; 
    public static final String PRJ_OBJ_C = PATH_OBJECT + "cprj_obj.gif";
    public static final String SAVEAS_DLG = PATH_WIZBAN + "saveas_wiz.png";
    
    /**
     * Image definition from org.eclipse.ui.internal.ide.IDEInternalWorkbenchImages#IMG_DLGBAN_SAVEAS_DLG
     */
    public static final String IMG_DLGBAN_SAVEAS_DLG = "IMG_DLGBAN_SAVEAS_DLG";
    private ToolboxLifecycleParticipant[] registeredTools;

    public WorkbenchWindowAdvisor createWorkbenchWindowAdvisor(IWorkbenchWindowConfigurer configurer)
    {
        return new ApplicationWorkbenchWindowAdvisor(configurer);
    }

    public String getInitialWindowPerspectiveId()
    {
        return PERSPECTIVE_ID;
    }

    /*
     * @see org.eclipse.ui.application.WorkbenchAdvisor#initialize(org.eclipse.ui.application.IWorkbenchConfigurer)
     */
    public void initialize(IWorkbenchConfigurer configurer)
    {
        // save the positions of windows etc...
        configurer.setSaveAndRestore(true);

        super.initialize(configurer);
        
        Bundle ideBundle = Platform.getBundle(IDE_PLUGIN);
        declareWorkbenchImage(configurer, ideBundle, IDE.SharedImages.IMG_OBJ_PROJECT, PRJ_OBJ,
                true);
        declareWorkbenchImage(configurer, ideBundle, IDE.SharedImages.IMG_OBJ_PROJECT_CLOSED, PRJ_OBJ_C, true);
        
        declareWorkbenchImage(configurer, ideBundle, IMG_DLGBAN_SAVEAS_DLG, SAVEAS_DLG, true);
        
        // register adapter
        IDE.registerAdapters();
    }

    private void declareWorkbenchImage(IWorkbenchConfigurer configurer, Bundle ideBundle, String symbolicName,
            String path, boolean shared)
    {
        URL url = ideBundle.getEntry(path);
        ImageDescriptor desc = ImageDescriptor.createFromURL(url);
        configurer.declareImage(symbolicName, desc, shared);
    }

    public boolean preShutdown()
    {
        if (!ToolboxHandle.getInstanceStore().getBoolean(ToolboxHandle.I_RESTORE_LAST_SPEC))
        {
            UIHelper.getActivePage().closeAllEditors(true);
            UIHelper.switchPerspective(getInitialWindowPerspectiveId());
        }
        
        try 
        {
            ToolboxParticipantManger.terminate(registeredTools);
        } catch (ToolboxLifecycleException e)
        {
            // TODO
            e.printStackTrace();
        }
        
        return super.preShutdown();
    }

    public void postStartup()
    {
        super.postStartup();
        
        try 
        {
            registeredTools = ToolboxParticipantManger.getRegisteredTools();
            ToolboxParticipantManger.initialize(registeredTools);
        } catch (ToolboxLifecycleException e)
        {
            // TODO
            e.printStackTrace();
        }
        
    }
    
    
}
