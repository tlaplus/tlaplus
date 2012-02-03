package org.lamport.tla.toolbox.util.pref;

import java.io.File;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ProjectScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.preferences.ScopedPreferenceStore;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.ui.preference.LibraryPathComposite;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.osgi.service.prefs.BackingStoreException;
import org.osgi.service.prefs.Preferences;

import util.SimpleFilenameToStream;

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
        projectPrefs.put(IPreferenceConstants.P_PROJECT_ROOT_FILE, rootFilename);
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
            String rootFileName = projectPrefs.get(IPreferenceConstants.P_PROJECT_ROOT_FILE, IPreferenceConstants.DEFAULT_NOT_SET);
System.out.println("footFileName = " + rootFileName);
            if (!IPreferenceConstants.DEFAULT_NOT_SET.equals(rootFileName))
            {
                return ResourceHelper.getLinkedFile(project, rootFileName);
            }
        } else {
            Activator.logInfo("projectPrefs is null");
        }
        return null;
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
        
        
        //store.get
        
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
            Activator.logError("Error storing the preference node", e);
        }
    }
    
    
    public static void clearPreferenceNode(Preferences preferenceNode)
    {
        try
        {
            preferenceNode.clear();
        } catch (BackingStoreException e)
        {
            Activator.logError("Error clearing the preference node", e);
        }
        
    }

    /**
     * Retrieves preference store with the project scope
     * @return a store instance
     */
    public static IPreferenceStore getProjectPreferenceStore(IProject project)
    {
        ProjectScope scope = new ProjectScope(project);
        ScopedPreferenceStore store = new ScopedPreferenceStore(scope, Activator.PLUGIN_ID /*Activator.getDefault().getBundle().getSymbolicName()*/);
        return store;
    }

    /**
     * Retrieves preference store with the workspace scope
     * @return a store instance
     */
    public static IPreferenceStore getInstancePreferenceStore()
    {
        IPreferenceStore store = Activator.getDefault().getPreferenceStore();
        return store;
    }

    
    /**
     * @deprecated
     */
    public static final String P_PROJECT_OPENED_MODULES = "ProjectOpenedModules";

    /**
     * Store the information about opened editors in project preferences
     * @param project
     * @param openedModules
     * @deprecated
     */
    public static void storeOpenedEditors(IProject project, String[] openedModules)
    {
        IEclipsePreferences projectPrefs = getProjectPreferences(project);
        Preferences opened = projectPrefs.node(P_PROJECT_OPENED_MODULES);
        
        clearPreferenceNode(opened);
        
        for (int i =0; i < openedModules.length; i++) 
        {
            opened.put(openedModules[i], openedModules[i]);
        }
        storeProferences(opened);
    }


    /**
     * Retrieves the information about the opened editors from project preferences
     * @param project
     * @return
     * @deprecated
     */
    public static String[] getOpenedEditors(IProject project) 
    {
        IEclipsePreferences projectPrefs = getProjectPreferences(project);
        Preferences opened = projectPrefs.node(P_PROJECT_OPENED_MODULES);
        
        String[] children = new String[0];
        try
        {
            children = opened.childrenNames();
        } catch (BackingStoreException e)
        {
            Activator.logError("Error reading preferences", e);
        }
        return children;
    }

	public static String[] getTLALibraryPath(IProject project) {
        final Set<String> locationList = new HashSet<String>();

        // Read project specific and general preferences (project take precedence over general ones) 
        String str = getProjectPreferenceStore(project).getString(LibraryPathComposite.LIBRARY_PATH_LOCATION_PREFIX);
        if ("".equals(str)) {
        	str = PreferenceStoreHelper.getInstancePreferenceStore().getString(LibraryPathComposite.LIBRARY_PATH_LOCATION_PREFIX);
        }
        
        // convert UI string into an array
        final String[] locations = str.split(LibraryPathComposite.ESCAPE_REGEX + LibraryPathComposite.LOCATION_DELIM);
        for (String location : locations) {
        	final String[] split = location.split(LibraryPathComposite.ESCAPE_REGEX + LibraryPathComposite.STATE_DELIM);
			if(Boolean.parseBoolean(split[1])) {
				locationList.add(split[0]);
        	}
		}
        
        return locationList.toArray(new String[locationList.size()]);
	}
	
	public static String getTLALibraryPathAsVMArg(IProject project) {
		final String[] tlaLibraryPath = getTLALibraryPath(project);
		
		if (tlaLibraryPath.length > 0) {
			final StringBuffer buf = new StringBuffer(tlaLibraryPath.length * 2);
			
			buf.append("-D" + SimpleFilenameToStream.TLA_LIBRARY + "=");
			
			for (final String location : tlaLibraryPath) {
				buf.append(location);
				buf.append(File.pathSeparator);
			}
			
			final String vmArg = buf.toString();
			
			return vmArg.substring(0, vmArg.length() - 1);
		} else {
			return "";
		}
	}
}
