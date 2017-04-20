// Copyright (c) Jan 30, 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.toolbox;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.net.URI;
import java.nio.file.FileAlreadyExistsException;
import java.nio.file.FileVisitResult;
import java.nio.file.FileVisitor;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.nio.file.attribute.BasicFileAttributes;
import java.nio.file.attribute.FileTime;
import java.util.Arrays;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
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
@SuppressWarnings("restriction")
public class Application implements IApplication {

	/* (non-Javadoc)
	 * @see org.eclipse.equinox.app.IApplication#start(org.eclipse.equinox.app.IApplicationContext)
	 */
	public Object start(IApplicationContext context) throws InvocationTargetException, InterruptedException {
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
		
		final Location instanceLocation = Platform.getInstanceLocation();
		
		// Check if the workspace has already been migrated to the new canonical
		// location starting with Toolbox 1.5.4. If it hasn't, we lookup the
		// previous location and copy its content to the canonical location
		// (unless for whatever reason the user decides to start fresh).
		// With a canonical location the cwd no longer matters from which the
		// Toolbox launcher is executed.
		if (!new File(instanceLocation.getURL().getFile() + File.separator + ".metadata" + File.separator).exists()) {
			new File(instanceLocation.getURL().getFile()).mkdir();
			
			final String previousInstanceLoc = getPreviousInstanceLocation(instanceLocation);
			if (previousInstanceLoc != null) {
				final String instanceLoc = instanceLocation.getURL().toExternalForm();
				if(!instanceLoc.equals(previousInstanceLoc)) {
					// Empty the recent workspaces to not show the dialog again.
					// Only clear it when the previous and current instance
					// location differ. This is the case when a user updates the
					// Toolbox and hits the restart button at the end of update.
					// This causes the Toolbox to restart with the previous
					// install location again.
					clearPreviousInstanceLocation(instanceLocation);
					
					// Open dialog and ask user to either import (migrate) the old workspace or create a fresh workspace.
					final MessageDialog md = new MessageDialog(PlatformUI.createDisplay().getActiveShell(), "Manually move Toolbox files.",
							null, 
									"Previously, your Toolbox used a different location to store its list of specifications and preferences. "
									+ "Starting with Toolbox release 1.5.4, the Toolbox keeps this data in a canonical location.\n\n"
									+ "If you do not let the Toolbox import this data, "
									+ "it will come up with default preferences and an empty spec explorer. "
									+ "You will have to manually configure the preferences and add your existing specifications.\n\n"
									+ "Click \"Import\" if you want the Toolbox to import the data now and continue Toolbox start-up.\n\n"
									+ "Click \"Start Fresh\" to continue Toolbox start-up and to manually add your specifications.",
							MessageDialog.QUESTION, new String[] {"Copy", "Start Fresh"}, 0);
					
					if (md.open() == 0) {
						final ProgressMonitorDialog pmd = new ProgressMonitorDialog(Display.getCurrent().getActiveShell());
						pmd.run(true, false, new IRunnableWithProgress() {
							public void run(final IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
								monitor.beginTask("Copying Toolbox metadata to new location.", IProgressMonitor.UNKNOWN);
								
								copyRecurively(
										Paths.get(URI.create(previousInstanceLoc + File.separator + ".metadata/")),
										Paths.get(URI.create(instanceLoc)), monitor);
								monitor.done();
							}
						});
					}
				}
			}
		}
		
		// The call to getStateLocation makes sure the instance location gets
		// initialized before we call .lock on it.
		StandaloneActivator.getDefault().getStateLocation();
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

	private static void clearPreviousInstanceLocation(final Location instanceLocation) {
		final ChooseWorkspaceData launchData = new ChooseWorkspaceData(instanceLocation.getDefault());
		launchData.setRecentWorkspaces(new String[0]);
		launchData.writePersistedData();
	}

	private static String getPreviousInstanceLocation(final Location instanceLocation) {
		// CWD is Eclipse infrastructure which stores the location of the
		// current workspace in a (text) file in the configuration area (Toolbox
		// installation directory) in 1.5.3. With version 1.5.4 of the Toolbox, we will
		// use this information below to migrate all workspaces to @user.home/.tlaplus.
		final ChooseWorkspaceData launchData = new ChooseWorkspaceData(instanceLocation.getDefault());
		final List<String> recentWorkspaces = Arrays.asList(launchData.getRecentWorkspaces());
		if (!recentWorkspaces.isEmpty()) {
			// Get the first non-null workspace. It is the most recently used one.
			for(int i = 0; i < recentWorkspaces.size(); i++) {
				if (recentWorkspaces.get(i) != null) {
					return recentWorkspaces.get(i);
				}
			}
		}
		return null;
	}
	
	// https://docs.oracle.com/javase/tutorial/displayCode.html?code=https://docs.oracle.com/javase/tutorial/essential/io/examples/Copy.java
	private static void copyRecurively(final Path src, final Path dst, final IProgressMonitor monitor)
			throws InvocationTargetException {
		try {
			final Path target = dst.resolve(src.getFileName());
			Files.walkFileTree(src, new FileVisitor<Path>() {
				public FileVisitResult preVisitDirectory(final Path dir, final BasicFileAttributes attrs)
						throws IOException {
					try {
						Files.copy(dir, target.resolve(src.relativize(dir)), StandardCopyOption.COPY_ATTRIBUTES);
					} catch (final FileAlreadyExistsException e) {
						// ignore
					}
					monitor.worked(1);
					return FileVisitResult.CONTINUE;
				}

				public FileVisitResult visitFile(final Path file, final BasicFileAttributes attrs) throws IOException {
					Files.copy(file, target.resolve(src.relativize(file)), StandardCopyOption.COPY_ATTRIBUTES);
					monitor.worked(1);
					return FileVisitResult.CONTINUE;
				}

				public FileVisitResult visitFileFailed(final Path file, final IOException exc) throws IOException {
					return FileVisitResult.CONTINUE;
				}

				public FileVisitResult postVisitDirectory(final Path dir, final IOException exc) throws IOException {
					final FileTime time = Files.getLastModifiedTime(dir);
					Files.setLastModifiedTime(target.resolve(src.relativize(dir)), time);
					monitor.worked(1);
					return FileVisitResult.CONTINUE;
				}
			});
		} catch (IOException e) {
			throw new InvocationTargetException(e);
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
