// Copyright (c) Jan 30, 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.toolbox;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.runtime.Platform;
import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.osgi.service.datalocation.Location;
import org.eclipse.osgi.util.NLS;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.internal.ide.ChooseWorkspaceData;

/**
 * This class controls all aspects of the application's execution
 * 
 * @author Simon Zambrovski
 */
public class Application implements IApplication {

	/* (non-Javadoc)
	 * @see org.eclipse.equinox.app.IApplication#start(org.eclipse.equinox.app.IApplicationContext)
	 */
	public Object start(IApplicationContext context) {
		Object argObject = context.getArguments().get(
				IApplicationContext.APPLICATION_ARGS);
		if (argObject != null && argObject instanceof String[]) {
			String[] args = (String[]) argObject;
			if (args.length != 0) {
				StandaloneActivator.getDefault().logDebug(context.getBrandingName() + " started with "
						+ args.length + " arguments.");
				for (int i = 0; i < args.length; i++) {
					StandaloneActivator.getDefault().logDebug(args[i]
							+ ((i == args.length - 1) ? "" : ", "));
				}
			} else {
				StandaloneActivator.getDefault().logDebug(context.getBrandingName()
						+ " started without arguments.");
			}
		}
		
		// The call to getStateLocation makes sure the instance location gets
		// initialized before we call .lock on it.
		StandaloneActivator.getDefault().getStateLocation();
		final Location instanceLocation = Platform.getInstanceLocation();
		// Only allow a single Toolbox instance per workspace to prevent data
		// corruption in the workspace files.
		try {
			if (!instanceLocation.lock()) {
				final File workspaceDirectory = new File(Platform.getInstanceLocation().getURL().getFile());
				if (workspaceDirectory.exists()) {
					MessageDialog.openError(PlatformUI.createDisplay().getActiveShell(), "Toolbox files cannot be locked",
							NLS.bind(
									"Could not launch the Toolbox because the associated workspace is currently in use by another Toolbox. Opening two instances on the same workspace leads to data corruption.\n\n"
											+ "If this is incorrect and there is no other Toolbox running, an earlier Toolbox terminated without releasing the lock. Please manually delete the lock file ''{0}'' and try restarting the Toolbox.",
											workspaceDirectory.getAbsolutePath()
											.concat(File.separator + ".metadata" + File.separator + ".lock")));
				}
				// We showed an error to the user, lets do a "clean" (0) exit to
				// not raise a second window with a detailed technical error.
				System.exit(0);
			}
		} catch (IOException e) {
			StandaloneActivator.getDefault().logError("Toolbox files cannot be locked", e);
			MessageDialog.openError(PlatformUI.createDisplay().getActiveShell(), "Toolbox files cannot be locked",
					"Could not launch the Toolbox because acquiring the associated workspace lock failed. We are sorry, this is a bug. Please get in contact with us.");
			// We showed an error to the user, lets do a "clean" (0) exit to
			// not raise a second window with a detailed technical error.
			System.exit(0);
		}

		// CWD is Eclipse infrastructure which stores the location of the
		// current workspace in a (text) file in the configuration area (Toolbox
		// installation directory). With version 1.5.4 of the Toolbox, we will
		// use this information to migrate all workspaces to @user.home/.tlaplus.
		final ChooseWorkspaceData launchData = new ChooseWorkspaceData(instanceLocation.getDefault());
		final Set s = new HashSet(Arrays.asList(launchData.getRecentWorkspaces()));
		// Remove null if recent workspaces above was empty (e.g. upon first toolbox startup).
		s.add(instanceLocation.getURL().toExternalForm());
		s.remove(null); 
		launchData.setRecentWorkspaces((String[]) s.toArray(new String[s.size()]));
		launchData.writePersistedData();

		Display display = PlatformUI.createDisplay();
		try {
			int returnCode = PlatformUI.createAndRunWorkbench(display,
					new ApplicationWorkbenchAdvisor());
			if (returnCode == PlatformUI.RETURN_RESTART) {
				return IApplication.EXIT_RESTART;
			}
			return IApplication.EXIT_OK;
		} finally {
			display.dispose();
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.equinox.app.IApplication#stop()
	 */
	public void stop() {
		final IWorkbench workbench = PlatformUI.getWorkbench();
		if (workbench == null)
			return;
		final Display display = workbench.getDisplay();
		display.syncExec(new Runnable() {
			public void run() {
				if (!display.isDisposed())
					workbench.close();
			}
		});
	}
}
