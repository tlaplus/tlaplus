package org.lamport.tla.toolbox.tool.prover.ui.util;

import java.io.File;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.preference.MainProverPreferencePage;

/**
 * A singleton which provides reference to the {@link IPath} instances for the TLAPM executable, should one exist, and
 * 	the Cygwin path, should the platform be appropriate.
 */
public class TLAPMExecutableLocator {
	public static final TLAPMExecutableLocator INSTANCE = new TLAPMExecutableLocator();
	
	private static final IPath DEFAULT_NIX_INSTALL_DIRECTORY = new Path("/usr/local/bin");
	private static final String NIX_EXECUTABLE_NAME = "tlapm";
	private static final String WINDOWS_EXECUTABLE_NAME = "tlapm.exe";
	
	public static boolean pathForExecutableIsUsable(final IPath path) {
		if (path == null) {
			return false;
		}
		
		final File f = path.toFile();
		return ((f != null)
				&& f.exists()
				&& f.canExecute());
	}
	
	
	private IPath tlapmPath;
	private final IPath cygwinPath;
	
	// The enclosing bundle is still Java 5 for some reason - move this to a lambda with Java 8+
	private final IPropertyChangeListener preferenceChangeListener = new IPropertyChangeListener() {
		public void propertyChange(final PropertyChangeEvent event) {
			if (MainProverPreferencePage.EXECUTABLE_LOCATION_KEY.equals(event.getProperty())) {
				final String location = (String) event.getNewValue();

				// Validation occurred in the preference page, so if we are getting this notification, the path is ok
				tlapmPath = new Path(location);
			}
		}
	};
	
	private TLAPMExecutableLocator() {
		final IPreferenceStore ips = ProverUIActivator.getDefault().getPreferenceStore();
		final String existingTLAPMPath = ips.getString(MainProverPreferencePage.EXECUTABLE_LOCATION_KEY);

        IPath tlapm = null;
		if (existingTLAPMPath.length() > 0) {
			final IPath path = new Path(existingTLAPMPath);
			
			if (pathForExecutableIsUsable(path)) {
				tlapm = path;
			}
		}
		
        IPath cygwin = null;
		if (Platform.getOS().equals(Platform.OS_WIN32)) {
            /*
             * Check if "C:/cygwin/usr/local/bin/tlapm.exe" exists.
             * If it does exist, that is the path. Else, the path is "tlapm". Setting
             * the path to "tlapm" assumes that it is in the system path.
             */
            final IPath defaultPath = new Path("C:/cygwin/usr/local/bin/" + WINDOWS_EXECUTABLE_NAME);
            final IPath defaultPath64 = new Path("C:/cygwin64/usr/local/bin/" + WINDOWS_EXECUTABLE_NAME);

            /*
             * Nowadays 64bit systems are common, thus also check c:/cygwin64/... preferring to use that
             */
			if (defaultPath64.toFile().exists()) {
				if (tlapm == null) {
					tlapm = defaultPath64;
				}
				cygwin = new Path("C:\\cygwin64\\bin");
			} else if (defaultPath.toFile().exists()) {
				if (tlapm == null) {
					tlapm = defaultPath;
				}
				cygwin = new Path("C:\\cygwin\\bin");
            } else if (tlapm == null) {
            	// Hopefully the Windows Path will sort it out
            	tlapm = new Path(WINDOWS_EXECUTABLE_NAME);
            }
		} else if (tlapm == null) {
			if (Platform.getOS().equals(Platform.OS_MACOSX) || Platform.getOS().equals(Platform.OS_LINUX)) {
				final String[] paths = System.getenv("PATH").split(":");
				boolean defaultDirectoryIncluded = false;
				
				for (final String path : paths) {
					final IPath parent = new Path(path);
					
					if (parent.equals(DEFAULT_NIX_INSTALL_DIRECTORY)) {
						defaultDirectoryIncluded = true;
					}
					
					final IPath executable = parent.append(NIX_EXECUTABLE_NAME);
					if (pathForExecutableIsUsable(executable)) {
						tlapm = executable;
						break;
					}
				}
				
				if (!defaultDirectoryIncluded && (tlapm == null)) {
					final IPath executable = new Path(DEFAULT_NIX_INSTALL_DIRECTORY + "/" + NIX_EXECUTABLE_NAME);
					if (pathForExecutableIsUsable(executable)) {
						tlapm = executable;
					}
				}
				
				if (tlapm == null) {
					// In some miraculous case the ProcessBuilder would get a different PATH environment and then
					//		find this, but as of 1.6.1 this is moot and will result in the menu items able to launch
					//		the prover not being enabled anyway...
					tlapm = new Path(NIX_EXECUTABLE_NAME);
				}
			} else {
				Activator.getDefault().logError("Platform [" + Platform.getOS() + "] is not supported.");
	        }
		}

		tlapmPath = tlapm;
		cygwinPath = cygwin;
		
		ips.addPropertyChangeListener(preferenceChangeListener);
	}
	
	/**
	 * @return true if the path to TLAPM exists and there is a file there which can be executed
	 */
	public boolean tlapmDoesExist() {
		return pathForExecutableIsUsable(tlapmPath);
	}
	
	/**
	 * @return this will be null on non-Windows platforms
	 */
	public IPath getCygwinPath() {
		return cygwinPath;
	}
	
	public IPath getTLAPMPath() {
		return tlapmPath;
	}
}
