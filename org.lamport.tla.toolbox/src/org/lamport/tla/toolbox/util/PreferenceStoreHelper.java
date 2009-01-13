package org.lamport.tla.toolbox.util;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ProjectScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.lamport.tla.toolbox.Activator;
import org.osgi.service.prefs.BackingStoreException;
import org.osgi.service.prefs.Preferences;

/**
 * Utils for accessing persistence storage
 * @author zambrovski
 */
public class PreferenceStoreHelper
{

    /**
     * Stores root file name in project preferences
     * @param project
     * @param rootFilename
     */
    public static void storeRootFilename(IProject project, String rootFilename)
    {
        IEclipsePreferences projectPrefs = getProjectPreferences(project);
        projectPrefs.put(IPreferenceConstants.PERSIST_PROJECT_ROOT_FILE, rootFilename);
        storeProferences(projectPrefs);        
    }

    /**
     * Retrieves project root file name
     * @param project
     * @return
     */
    public static IFile readProjectRootFile(IProject project)
    {
        IEclipsePreferences projectPrefs = getProjectPreferences(project);
        if (projectPrefs != null)
        {
            String rootFileName = projectPrefs.get(IPreferenceConstants.PERSIST_PROJECT_ROOT_FILE, IPreferenceConstants.DEFAULT_NOT_SET);
            if (!IPreferenceConstants.DEFAULT_NOT_SET.equals(rootFileName))
            {
                return ResourceHelper.getLinkedFile(project, rootFileName);
            }
        }
        return null;
    }

    /**
     * Store the information about opened editors
     * @param project
     * @param openedModules
     */
    public static void storeOpenedEditors(IProject project, String[] openedModules)
    {
        IEclipsePreferences projectPrefs = getProjectPreferences(project);
        Preferences opened = projectPrefs.node(IPreferenceConstants.PERSIST_PROJECT_OPENED_MODULES);
        
        clearPreferenceNode(opened);
        
        for (int i =0; i < openedModules.length; i++) 
        {
            opened.put(openedModules[i], openedModules[i]);
        }
        storeProferences(opened);        
    }

    /**
     * Retrieves the information about the opened editors
     * @param project
     * @return
     */
    public static String[] getOpenedEditors(IProject project) 
    {
        IEclipsePreferences projectPrefs = getProjectPreferences(project);
        Preferences opened = projectPrefs.node(IPreferenceConstants.PERSIST_PROJECT_OPENED_MODULES);
        
        String[] children = new String[0];
        try
        {
            children = opened.childrenNames();
        } catch (BackingStoreException e)
        {
            e.printStackTrace();
        }
        return children;
    }

    
    
    /**
     * Retrieves project preference node
     * @param project 
     * @return
     */
    public static IEclipsePreferences getProjectPreferences(IProject project)
    {
        if (project == null ) 
        {
            return null;
        }
        ProjectScope scope = new ProjectScope(project);
        IEclipsePreferences projectNode = scope.getNode(Activator.PLUGIN_ID);
        return projectNode;
    }
    /**
     * Stores the preferences to disk
     * @param preferences
     */
    public static void storeProferences(Preferences preferences)
    {
        try
        {
            preferences.flush();
        } catch (BackingStoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }
    
    
    /**
     * @param opened
     */
    public static void clearPreferenceNode(Preferences preferenceNode)
    {
        try
        {
            preferenceNode.clear();
        } catch (BackingStoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        
    }

    

}
