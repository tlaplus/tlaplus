package org.lamport.tla.toolbox.tool.prover.ui.util;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.lamport.tla.toolbox.Activator;

/**
 * A singleton which provides reference to the {@link IPath} instances for the TLAPM executable, should one exist, and
 * 	the Cygwin path, should the platform be appropriate.
 */
public class TLAPMExecutableLocator {
	public static final TLAPMExecutableLocator INSTANCE = new TLAPMExecutableLocator();
	
	
	private final IPath tlapmPath;
	private final IPath cygwinPath;
	
	private TLAPMExecutableLocator() {
        // the default tlapm command on all systems if no complete tlapm path can be found.
        IPath tlapm = new Path("tlapm");
        IPath cygwin = null;

		if (Platform.getOS().equals(Platform.OS_WIN32)) {
            /*
             * Check if "C:/cygwin/usr/local/bin/tlapm.exe" exists.
             * If it does exist, that is the path. Else, the path is "tlapm". Setting
             * the path to "tlapm" assumes that it is in the system path.
             */
            final IPath defaultPath = new Path("C:/cygwin/usr/local/bin/tlapm.exe");
            final IPath defaultPath64 = new Path("C:/cygwin64/usr/local/bin/tlapm.exe");

			if (defaultPath.toFile().exists()) {
				tlapm = defaultPath;

                /*
                 * If cygwin path is specified, use that. If not
                 * use the default cygwin path : 
                 * "C:\cygwin\bin"
                 */
				cygwin = new Path("C:\\cygwin\\bin");
            }
            /*
             * Nowadays 64bit systems are common, thus also check c:/cygwin64/... preferring to use that
             */
			else if (defaultPath64.toFile().exists()) {
				tlapm = defaultPath64;
				cygwin = new Path("C:\\cygwin64\\bin");
            }
		} else if (Platform.getOS().equals(Platform.OS_MACOSX) || Platform.getOS().equals(Platform.OS_LINUX)) {
            /*
             * Check if "/usr/local/bin/tlapm" exists.
             * If it does exist, that is the path. Else, the path is tlapm. Setting
             * the path to "tlapm" assumes that it is in the system path.
             */
            final IPath defaultPath = new Path("/usr/local/bin/tlapm");

			if (defaultPath.toFile().exists()) {
				tlapm = defaultPath;
            }
		} else {
			Activator.getDefault().logError("Platform [" + Platform.getOS() + "] is not supported.");
        }

		tlapmPath = tlapm;
		cygwinPath = cygwin;
	}

	/**
	 * @return true if the path to TLAPM exists and there is a file there which can be executed
	 */
	public boolean tlapmDoesExist() {
		return ((tlapmPath != null)
					&& (tlapmPath.toFile() != null)
					&& tlapmPath.toFile().exists()
					&& tlapmPath.toFile().canExecute());
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
