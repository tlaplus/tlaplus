package org.lamport.tla.toolbox.test;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.finders.UIThreadRunnable;
import org.eclipse.swtbot.swt.finder.results.VoidResult;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.WorkbenchException;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;

/**
 * @see http://www.ralfebert.de/articles/swtbot/
 */
public abstract class RCPTestSetupHelper {
	
	public static void beforeClass() {
		UIThreadRunnable.syncExec(new VoidResult() {
			public void run() {
				resetWorkbench();
				resetToolbox();
				
				// close browser-based welcome screen (if open)
				SWTWorkbenchBot bot = new SWTWorkbenchBot();
				try {
					SWTBotView welcomeView = bot.viewByTitle("Welcome");
					welcomeView.close();
				} catch (WidgetNotFoundException e) {
					return;
				}
			}
		});
	}
	
    public static void afterClass() {
        UIThreadRunnable.syncExec(new VoidResult() {
            public void run() {
                resetWorkbench();
            }
        });
    }

    /**
     * Close all open windows, editors, perspectives. Open and reset default perspective.
     */
    private static void resetWorkbench() {
        try {
            IWorkbench workbench = PlatformUI.getWorkbench();
            IWorkbenchWindow workbenchWindow = workbench.getActiveWorkbenchWindow();
            IWorkbenchPage page = workbenchWindow.getActivePage();
            
            Shell activeShell = Display.getCurrent().getActiveShell();
            if (activeShell != null && activeShell != workbenchWindow.getShell()) {
                activeShell.close();
            }
            
            page.closeAllEditors(false);
            page.resetPerspective();
            
            String defaultPerspectiveId = workbench.getPerspectiveRegistry().getDefaultPerspective();
            workbench.showPerspective(defaultPerspectiveId, workbenchWindow);
            page.resetPerspective();
            
            page.showView("org.eclipse.ui.internal.introview");
        } catch (WorkbenchException e) {
            throw new RuntimeException(e);
        }
    }

	/**
	 * Removes all existing specs and models
	 */
	private static void resetToolbox() {
		final WorkspaceSpecManager specManager = Activator.getSpecManager();
		// assume recently opened specs means all existing specs :)
		final Spec[] specs = specManager.getRecentlyOpened();
		for (int i = 0; i < specs.length; i++) {
			specManager.removeSpec(specs[i], new NullProgressMonitor());
		}
	}
}
