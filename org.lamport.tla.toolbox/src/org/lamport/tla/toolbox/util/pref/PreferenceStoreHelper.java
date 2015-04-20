package org.lamport.tla.toolbox.util.pref;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ProjectScope;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.preferences.ScopedPreferenceStore;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.util.ResourceHelper;
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
	public static void storeRootFilename(IProject project, String rootFilename) {
		// If this condition does not hold, the subsequent code but also
		// AddModuleHandler will not work. The claim is that spec files are
		// always in the parent folder of the IProject.
		final IPath path = new Path(rootFilename);
		Assert.isTrue(ResourceHelper.isProjectParent(path.removeLastSegments(1), project));
		// Store the filename *without* any path information, but prepend the
		// magical PARENT-1-PROJECT-LOC. It indicates that the file can be found
		// *one* level up (hence the "1") from the project location.
		// readProjectRootFile can later easily deduce the relative location of
		// the file.
		rootFilename = ResourceHelper.PARENT_ONE_PROJECT_LOC + path.lastSegment();
        IEclipsePreferences projectPrefs = getProjectPreferences(project);
        projectPrefs.put(IPreferenceConstants.P_PROJECT_ROOT_FILE, rootFilename);
        storePreferences(projectPrefs);        
    }

    /**
     * Retrieves project root file name
     * @param project
     * @return
     */
	public static IFile readProjectRootFile(IProject project) {
		final IEclipsePreferences projectPrefs = getProjectPreferences(project);
		if (projectPrefs != null) {
			String rootFileName = projectPrefs.get(IPreferenceConstants.P_PROJECT_ROOT_FILE,
					IPreferenceConstants.DEFAULT_NOT_SET);
			if (!IPreferenceConstants.DEFAULT_NOT_SET.equals(rootFileName)) {
				final IPath path = new Path(rootFileName);
				if (path.isAbsolute()) {
					// Convert a legacy (absolute) path to the new relative one
					// with the magic PARENT_PROJECT_LOC prefix.
					rootFileName = ResourceHelper.PARENT_ONE_PROJECT_LOC + path.lastSegment(); 
					convertAbsoluteToRelative(projectPrefs, rootFileName);
				}
				final IFile linkedFile = ResourceHelper.getLinkedFile(project, rootFileName);
				Activator.getDefault().logDebug(
						"footFileName = " + (linkedFile != null ? linkedFile.getLocation().toOSString() : null));
				return linkedFile;
			}
		} else {
			Activator.getDefault().logInfo("projectPrefs is null");
		}
		return null;
	}

	private static void convertAbsoluteToRelative(final IEclipsePreferences projectPrefs, final String path) {
		projectPrefs.remove(IPreferenceConstants.P_PROJECT_ROOT_FILE);
		projectPrefs.put(IPreferenceConstants.P_PROJECT_ROOT_FILE, path);
		try {
			projectPrefs.flush();
			projectPrefs.sync();
		} catch (BackingStoreException notExpectedToHappen) {
			Activator.getDefault().logError(
					"Failed to store rewritten absolute to relative root file name: " + path,
					notExpectedToHappen);
		}
	}

    /**
     * Retrieves project preference node
     * @param project 
     * @return
     */
	private static IEclipsePreferences getProjectPreferences(IProject project)
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
    private static void storePreferences(Preferences preferences)
    {
        try
        {
            preferences.flush();
        } catch (BackingStoreException e)
        {
            Activator.getDefault().logError("Error storing the preference node", e);
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
}
