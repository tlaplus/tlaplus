package org.lamport.tla.toolbox.util;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.NotEnabledException;
import org.eclipse.core.commands.NotHandledException;
import org.eclipse.core.commands.ParameterizedCommand;
import org.eclipse.core.commands.common.NotDefinedException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.e4.core.contexts.IEclipseContext;
import org.eclipse.e4.ui.model.application.ui.MElementContainer;
import org.eclipse.e4.ui.model.application.ui.MUIElement;
import org.eclipse.e4.ui.model.application.ui.basic.MPart;
import org.eclipse.jface.action.IStatusLineManager;
import org.eclipse.jface.dialogs.IconAndMessageDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.window.IShellProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.BusyIndicator;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Spinner;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.eclipse.ui.IPerspectiveListener;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.WorkbenchException;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.handlers.IHandlerService;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.part.MultiPageEditorPart;
import org.eclipse.ui.texteditor.ITextEditor;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.ui.handler.OpenSpecHandler;
import org.lamport.tla.toolbox.ui.perspective.InitialPerspective;
import org.lamport.tla.toolbox.ui.property.GenericSelectionProvider;
import org.lamport.tla.toolbox.ui.view.ToolboxWelcomeView;

import pcal.Region;
import pcal.TLAtoPCalMapping;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.NonLeafProofNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.ProofNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.TheoremNode;
import tla2sany.semantic.ThmOrAssumpDefNode;
import tla2sany.st.Location;

/**
 * A Helper for handling the RCP Objects like windows, editors and views
 * 
 * @version $Id$
 * @author zambrovski
 */
public class UIHelper {

	/**
	 * Closes all windows with a perspective
	 * 
	 * @param perspectiveId
	 *            a perspective Id pointing the perspective
	 */
	public static void closeWindow(String perspectiveId) {
		IWorkbench workbench = Activator.getDefault().getWorkbench();
		// hide intro
		if (InitialPerspective.ID.equals(perspectiveId)) {
			workbench.getIntroManager().closeIntro(workbench.getIntroManager().getIntro());
		}

		IWorkbenchWindow[] windows = workbench.getWorkbenchWindows();

		// closing the perspective opened in a window
		for (int i = 0; i < windows.length; i++) {
			IWorkbenchPage page = windows[i].getActivePage();
			if (page != null && page.getPerspective() != null && perspectiveId.equals(page.getPerspective().getId())) {
				windows[i].close();
			}
		}
	}

	/**
	 * Opens the perspective in a new window on the right of the original window
	 * 
	 * @param perspectiveId
	 * @param input
	 * @param width
	 *            - width of new window
	 * @return
	 * @deprecated
	 */
	public static IWorkbenchWindow openPerspectiveInWindowRight(String perspectiveId, IAdaptable input, int width) {
		IWorkbench workbench = Activator.getDefault().getWorkbench();
		Rectangle bounds = workbench.getActiveWorkbenchWindow().getShell().getBounds();

		IWorkbenchWindow window = openPerspectiveInNewWindow(perspectiveId, input);
		window.getShell().setBounds(bounds.x + bounds.width, bounds.y, width, bounds.height);

		return window;
	}

	/**
	 * Opens the new window containing the new perspective
	 * 
	 * @param perspectiveId
	 *            new perspective
	 * @param input
	 *            IAdaptable, or null if no input
	 * @return IWorkbenchWindow instance
	 * 
	 */
	public static IWorkbenchWindow openPerspectiveInNewWindow(String perspectiveId, IAdaptable input) {
		IWorkbench workbench = Activator.getDefault().getWorkbench();
		IWorkbenchWindow window = null;
		try {
			// avoids flicking, from implementation above
			window = workbench.openWorkbenchWindow(perspectiveId, input);

			// show intro
			if (InitialPerspective.ID.equals(perspectiveId) && workbench.getIntroManager().hasIntro()) {
				// IIntroPart intro =
				workbench.getIntroManager().showIntro(window, true);
			}

		} catch (WorkbenchException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return window;
	}

	/**
	 * Opens a view
	 * 
	 * @param viewId
	 * @return the reference to the view
	 */
	public static IViewPart openView(String viewId) {
		IViewPart view = null;
		try {
			IWorkbenchPage activePage = getActivePage();
			if (activePage != null) {
				view = activePage.showView(viewId);
			}
		} catch (PartInitException e) {
			Activator.getDefault().logError("Error opening a view " + viewId, e);
		}
		return view;
	}

	/**
	 * Opens a view but does *not* give it focus (useful for informational views
	 * that should not distract the user's workflow (e.g. typing in the editor).
	 * 
	 * @param viewId
	 * @return the reference to the view
	 */
	public static IViewPart openViewNoFocus(final String viewId) {
		IViewPart view = null;
		try {
			IWorkbenchPage activePage = getActivePage();
			if (activePage != null) {
				view = activePage.showView(viewId, null, IWorkbenchPage.VIEW_VISIBLE);
			}
		} catch (PartInitException e) {
			Activator.getDefault().logError("Error opening a view " + viewId, e);
		}
		return view;
	}

	/**
	 * Find a view if on the page
	 * 
	 * @param viewId
	 * @return
	 */
	public static IViewPart findView(String viewId) {
		IViewPart view = null;
		IWorkbenchPage activePage = getActivePage();
		if (activePage != null) {
			view = activePage.findView(viewId);
		}
		return view;
	}

	/**
	 * Checks weather the view is shown
	 * 
	 * @param id
	 *            view Id
	 * @return
	 */
	public static boolean isViewShown(String id) {
		return (getActivePage().findView(id) == null);

	}

	/**
	 * Hides a view
	 * 
	 * @param id
	 *            Id of the view to hide
	 */
	public static void hideView(String id) {
		IViewPart findView = getActivePage().findView(id);
		if (findView != null) {
			getActivePage().hideView(findView);
		}
	}

	/**
	 * Returns the perspective to its initial layout
	 * 
	 * @param perspectiveId
	 */
	public static void revertPerspecive(String perspectiveId) {
		IWorkbench workbench = Activator.getDefault().getWorkbench();
		IPerspectiveDescriptor descriptor = workbench.getPerspectiveRegistry().findPerspectiveWithId(perspectiveId);
		workbench.getPerspectiveRegistry().revertPerspective(descriptor);
	}

	/**
	 * Attaches the perspective listener to active window
	 * 
	 * @param listener
	 */
	public static void addPerspectiveListener(IPerspectiveListener listener) {
		IWorkbench workbench = Activator.getDefault().getWorkbench();
		IWorkbenchWindow window = workbench.getActiveWorkbenchWindow();
		window.addPerspectiveListener(listener);
	}

	/**
	 * Switch current perspective
	 * 
	 * @param perspectiveId
	 * @return
	 */
	public static IWorkbenchPage switchPerspective(String perspectiveId) {
		Assert.isNotNull(perspectiveId, "PerspectiveId is null");
		IWorkbench workbench = PlatformUI.getWorkbench();
		IWorkbenchWindow window = getActiveWindow();
		Assert.isNotNull(workbench, "Workbench is null");
		Assert.isNotNull(window, "Window is null");
		try {
			IWorkbenchPage page = workbench.showPerspective(perspectiveId, window);

			// show intro
			if (InitialPerspective.ID.equals(perspectiveId) && workbench.getIntroManager().hasIntro()) {
				page.resetPerspective();
				// We are no longer showing the Intro view. The following will
				// probably
				// be replaced by something that shows the view we want. 09 Oct
				// 2009
				// workbench.getIntroManager().showIntro(window, false);
				openView(ToolboxWelcomeView.ID);

			}

			return page;
		} catch (WorkbenchException e) {
			Activator.getDefault().logError("Error switching a perspective to " + perspectiveId, e);
		}

		return null;
	}

	/**
	 * Retrieves the id of currently selected perspective
	 * 
	 * @return
	 */
	public static String getActivePerspectiveId() {
		return UIHelper.getActivePage().getPerspective().getId();
	}

	/**
	 * Convenience method to reduce client dependencies
	 * 
	 * @param editorId
	 * @param file
	 * @return
	 */
	public static IEditorPart openEditor(String editorId, IFile file) {
		return openEditor(editorId, new FileEditorInput(file));
	}

	/**
	 * Opens an editor in current workbench window
	 * 
	 * @param editorId
	 * @param input
	 * @return the created or reopened IEditorPart
	 */
	public static IEditorPart openEditor(String editorId, IEditorInput input) {
		final IWorkbenchPage activePage = getActivePage();
		if (activePage != null) {
			try {

				final IEditorPart openEditor = activePage.openEditor(input, editorId);

				// Trigger re-evaluation of the handler enablement state by
				// cycling the activepage. Cycling the active page causes an
				// event to be fired inside the selection service.
				// During this time, there will be no active page!
				getActiveWindow().setActivePage(null);
				getActiveWindow().setActivePage(activePage);

				return openEditor;
			} catch (PartInitException e) {
				e.printStackTrace();
			}
		}
		return null;
	}

	/**
	 * Convenience method to reduce client dependencies
	 * 
	 * @param editorId
	 * @param file
	 * @return
	 * @throws PartInitException
	 */
	public static IEditorPart openEditorUnchecked(String editorId, IFile file) throws PartInitException {
		return openEditorUnchecked(editorId, new FileEditorInput(file));
	}

	/**
	 * Opens an editor in current workbench window
	 * 
	 * @param editorId
	 * @param input
	 * @return the created or reopened IEditorPart
	 * @throws PartInitException
	 */
	public static IEditorPart openEditorUnchecked(String editorId, IEditorInput input) throws PartInitException {
		final IWorkbenchPage activePage = getActivePage();
		if (activePage != null) {
			final IEditorPart openEditor = activePage.openEditor(input, editorId);

			// Trigger re-evaluation of the handler enablement state by
			// cycling the activepage. Cycling the active page causes an
			// event to be fired inside the selection service.
			// During this time, there will be no active page!
			getActiveWindow().setActivePage(null);
			getActiveWindow().setActivePage(activePage);

			return openEditor;
		}
		return null;
	}

	/**
	 * Retrieves active window
	 * 
	 * @return
	 */
	public static IWorkbenchWindow getActiveWindow() {
		return PlatformUI.getWorkbench().getActiveWorkbenchWindow();
	}

	/**
	 * Retrieves active page
	 * 
	 * @return
	 */
	public static IWorkbenchPage getActivePage() {
		final IWorkbenchWindow window = getActiveWindow();
		if (window == null) {
			// try to get a not null window
			final IWorkbench workbench = PlatformUI.getWorkbench();
			if (workbench != null) {
				IWorkbenchWindow[] workbenchWindows = workbench.getWorkbenchWindows();
				for (int i = 0; i < workbenchWindows.length; i++) {
					if (workbenchWindows[i] != null) {
						return workbenchWindows[i].getActivePage();
					}
				}
				return null;
			} else {
				return null;
			}
		}
		return window.getActivePage();
	}

	/**
	 * Retrieves the list of resources opened in editor
	 * 
	 * @return an array of paths of opened resources
	 */
	public static String[] getOpenedResources() {
		IEditorReference[] references = getActivePage().getEditorReferences();
		String[] openedResources = new String[references.length];

		for (int i = 0; i < references.length; i++) {
			openedResources[i] = references[i].getContentDescription();
		}

		return openedResources;
	}

	/**
	 * Runs a command with parameters
	 * 
	 * Note added by LL: In case you don't have time to read the extensive
	 * comment above written by Simon, here is my attempt at a condensed
	 * version. This method takes a commandId, which was registered in the
	 * plugin.xml file as a command for the org.eclipse.ui.commands extension,
	 * as the name of a command, and invokes the Eclipse magic that calls the
	 * execute(...) method of the Handler class for the handler that was
	 * associated with that command by adding it to the extension
	 * org.eclipse.ui.handlers (in some plugin.xml file) and giving it the
	 * command's Id. (I'm surprised that Eclipse was able to do that with so few
	 * levels of indirection.)
	 * 
	 * The parameters argument seems to be used as follows for passing arguments
	 * to the execute(e) command. The caller of UIHelper.java packages the
	 * parameters as a HashMap by executing
	 * 
	 * HashMap parameters = new HashMap();
	 * parameters.put(ParameterNameAsAString, parameterValue); ...
	 * 
	 * The execute(event) command fetches the parameters by executing
	 * 
	 * ... = event.getParameter((String) ParameterNameAsString);
	 * 
	 * @param commandId
	 * @param parameters
	 * @return
	 */
	public static Object runCommand(String commandId, Map<String, String> parameters) {
		// Do not rely on the UI to be up and running when trying to execute a
		// command
		IHandlerService handlerService = (IHandlerService) PlatformUI.getWorkbench().getService(IHandlerService.class);
		ICommandService commandService = (ICommandService) PlatformUI.getWorkbench().getService(ICommandService.class);

		// Guard against NPEs anyway (e.g. some asynchronous jobs might try to
		// run a
		// command after shutdown has been called on the workbench in which case
		// either service might be null
		if (handlerService == null || commandService == null) {
			Activator.getDefault().logInfo(
					"No IHandlerService|ICommandService available while trying to execute a command");
			return null;
		}

		try {
			Command command = commandService.getCommand(commandId);
			ParameterizedCommand pCommand = ParameterizedCommand.generateCommand(command, parameters);
			return handlerService.executeCommand(pCommand, null);
		} catch (NotDefinedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (NotEnabledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (NotHandledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (ExecutionException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		return null;
	}

	/**
     * 
     */
	public static List<IEditorReference> checkOpenResources(String title, String message) {
		List<IEditorReference> dirtyEditors = new LinkedList<IEditorReference>();
		IEditorReference[] references = UIHelper.getActivePage().getEditorReferences();
		if (references != null) {
			for (int i = 0; i < references.length; i++) {
				if (references[i].isDirty()) {
					dirtyEditors.add(references[i]);
				}
			}
		}

		if (dirtyEditors.size() > 0) {
			boolean saveFiles = MessageDialog.openQuestion(getShell(), title, message);
			if (saveFiles) {
				// TODO provide a way to select what to save and what to drop
				// TODO provide a way to cancel
				return dirtyEditors;
			}
		}

		return new LinkedList<IEditorReference>();
	}

	/**
	 * If there are unsaved modules open, this prompts the user to save the
	 * modules with an OK/Cancel dialog. If the user selects OK, this saves the
	 * modules before returning, other wise it does not.
	 * 
	 * @return false if a dialog is opened and the user selects cancel or the
	 *         user closes the dialog without pressing OK or cancel, true
	 *         otherwise
	 */
	public static boolean promptUserForDirtyModules() {
		final List<IEditorReference> dirtyEditors = new LinkedList<IEditorReference>();
		IEditorReference[] references = UIHelper.getActivePage().getEditorReferences();
		if (references != null) {
			for (int i = 0; i < references.length; i++) {
				try {
					if (references[i].isDirty() && references[i].getEditorInput().getName().endsWith(".tla")) {
						dirtyEditors.add(references[i]);
					}
				} catch (PartInitException e) {
					Activator.getDefault().logError("Error getting unsaved resources.", e);
				}
			}
		}

		if (dirtyEditors.size() > 0) {

			// opens a OK/cancel dialog
			boolean saveFiles = MessageDialog.openConfirm(getShell(), "Modified resources",
					"Some resources are modified.\nDo you want to save the modified resources?");

			if (saveFiles) {
				// User selected OK
				runUISync(new Runnable() {

					public void run() {
						// save modified resources
						Iterator<IEditorReference> it = dirtyEditors.iterator();
						while (it.hasNext()) {
							IEditorReference reference = it.next();
							IEditorPart editor = reference.getEditor(false);
							if (editor != null) {
								editor.doSave(new NullProgressMonitor());
							}
						}
					}
				});
			}

			return saveFiles;
		}

		// no dirty modules
		// no dialog opened
		return true;
	}

	/**
	 * Returns a possibly platform dependent {@link FileDialog} that allows the
	 * user to select a file or type in a file name.
	 * 
	 * @param shell
	 * @return
	 */
	public static FileDialog getFileDialog(Shell shell) {
		FileDialog openFileDialog = null;

		// platform dependent code!
		if (Platform.getOS().equals(Platform.OS_MACOSX)) {
			// On Mac, we need a Save dialog in order to allow
			// the user to type in a file name as well as select one.
			//
			// Mac: SWT.OPEN and SWT.MULTI styles do *not* support file creation
			// (contrary to Linux/Win). However, the Toolbox uses a single
			// FileDialog to open existing *and* to create new specifications.
			// SWT.SAVE is the only FileDialog style that supports this use
			// case, but it comes at a price. The FileDialog's label is
			// rather unintuitive ("Save" and not "Open"). The filter extensions
			// doesn't work either. Even files matching the filter (*.tla) are
			// greyed out (see org.eclipse.swt.internal.cocoa.NSSavePanel).
			openFileDialog = new FileDialog(shell, SWT.SAVE);
			// since this could be a save as dialog trying
			// to act as an open dialog, the default will be
			// to not prompt the user to overwrite a file because
			// that would not make any sense in an open file dialog.
			openFileDialog.setOverwrite(false);
		} else {
			// On other platforms, an open dialog is sufficient as it
			// supports opening existing as well as creating new files.
			openFileDialog = new FileDialog(shell, SWT.OPEN);
		}

		return openFileDialog;
	}

	/**
	 * Retrieves active shell
	 * 
	 * @return a parent shell of the active window
	 */
	public static Shell getShell() {
		return getActiveWindow().getShell();
	}

	/**
	 * Added by LL on 11 June 2010. This snippet of code was used in several
	 * places, so I turned it into a method. I have no idea exactly what it's
	 * doing.
	 * 
	 * @return The current display, whatever that means.
	 */
	public static Display getCurrentDisplay() {
		Display display = Display.getCurrent();
		if (display == null) {
			// TODO fix me:
			// Creating a new display appears to be
			// forbidden on Mac OS x if the workbench has already been shutdown/
			// if not called from within the main (UI) thread
			return Display.getDefault();
		}
		return display;
	}

	/**
	 * Runs a task in synchronous UI thread.
	 * 
	 * See {@link Display#syncExec(Runnable)} for an explanation of what this
	 * method really does.
	 * 
	 * @param task
	 */
	public static void runUISync(Runnable task) {
		Display display = getCurrentDisplay();
		display.syncExec(task);
	}

	/**
	 * Runs a task in asynchronous UI thread.
	 * 
	 * See {@link Display#asyncExec(Runnable)} for an explanation of what this
	 * method really does.
	 * 
	 * @param task
	 */
	public static void runUIAsync(Runnable task) {
		Display display = getCurrentDisplay();
		display.asyncExec(task);
	}

	/**
	 * Determines if given perspective is shown
	 * 
	 * @param id
	 * @return true if the perspective with current id is shown, false otherwise
	 */
	public static boolean isPerspectiveShown(String perspectiveId) {
		if (perspectiveId == null || perspectiveId.equals("")) {
			return false;
		}
		IWorkbenchWindow[] workbenchWindows = PlatformUI.getWorkbench().getWorkbenchWindows();
		for (int i = 0; i < workbenchWindows.length; i++) {
			IPerspectiveDescriptor[] openPerspectives = workbenchWindows[i].getActivePage().getOpenPerspectives();
			for (int j = 0; j < openPerspectives.length; j++) {
				if (perspectiveId.equals(openPerspectives[j].getId())) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Registers a control to the context This can only be used within the
	 * plug-in org.lamport.tla.toolbox
	 * 
	 * @param control
	 *            control to register
	 * @param localContext
	 *            the context id relative to org.lamport.tla.toolbox plug-in ID <br>
	 *            Note: there should be a corresponding context ID defined in
	 *            the contexts.xml defining the context for current ID.
	 */
	public static void setHelp(Control control, String localContext) {
		PlatformUI.getWorkbench().getHelpSystem().setHelp(control, Activator.PLUGIN_ID + "." + localContext);
	}

	/**
	 * Convenience method
	 * 
	 * @see {@link Activator#imageDescriptorFromPlugin(String, String)}
	 */
	public static ImageDescriptor imageDescriptor(String imageFilePath) {
		return Activator.imageDescriptorFromPlugin(Activator.PLUGIN_ID, imageFilePath);
	}

	/**
	 * Retrieves a shell provider of currently active shell
	 * 
	 * @return
	 */
	public static IShellProvider getShellProvider() {
		return new IShellProvider() {

			public Shell getShell() {
				return UIHelper.getShell();
			}
		};
	}

	/**
	 * Retrieves the selection provider for files in the active editor
	 * 
	 * @return
	 */
	public static ISelectionProvider getActiveEditorFileSelectionProvider() {
		return new GenericSelectionProvider() {

			public ISelection getSelection() {
				IEditorInput input = getActiveEditor().getEditorInput();
				if (input instanceof FileEditorInput) {
					IFile resource = ((FileEditorInput) input).getFile();
					return new StructuredSelection(resource);
				}
				return null;
			}

			public void setSelection(ISelection selection) {
				throw new UnsupportedOperationException("This selection provider is read-only");
			}

		};
	}

	/**
	 * Retrieves the control from the viewer
	 */
	public static Control getWidget(Object control) {
		if (control instanceof Viewer) {
			return ((Viewer) control).getControl();
		} else if (control instanceof Text) {
			return (Text) control;
		} else if (control instanceof Button) {
			return (Control) control;
		} else if (control instanceof Spinner) {
			return (Control) control;
		} else if (control instanceof Control) {
			// why not return the control when object is instanceof control?
			return null;
		}

		return null;
	}

	public static void showDynamicHelp() {
		// This may take a while, so use the busy indicator
		BusyIndicator.showWhile(null, new Runnable() {
			public void run() {
				getActiveWindow().getWorkbench().getHelpSystem().displayDynamicHelp();
				// the following ensure that the help view receives focus
				// prior to adding this, it would not receive focus if
				// it was opened into a folder or was already
				// open in a folder in which another part had focus
				IViewPart helpView = findView("org.eclipse.help.ui.HelpView");
				if (helpView != null && getActiveWindow() != null && getActiveWindow().getActivePage() != null) {
					getActiveWindow().getActivePage().activate(helpView);
				}
			}
		});
	}

	/**
	 * @see UIHelper#jumpToLocation(Location, boolean)
	 */
	public static void jumpToLocation(final Location location) {
		jumpToLocation(location, false);
	}

	/**
	 * Reveals and highlights the given location in a TLA editor. Opens an
	 * editor on the module if an editor is not already open on it.
	 * 
	 * @param location
	 */
	public static void jumpToLocation(Location location, final boolean jumpToPCal) {
		if (location != null) {
			// the source of a location is the module name
			IResource moduleResource = ResourceHelper.getResourceByModuleName(location.source());
			if (moduleResource != null && moduleResource.exists()) {
				/*
				 * Now, retrieve a representation of the resource as a document.
				 * To do this, we use a FileDocumentProvider.
				 * 
				 * We disconnect the document provider in the finally block for
				 * the following try block in order to avoid a memory leak.
				 */
				IDocument document = null;

				// since we know that the editor uses file based editor
				// representation
				FileEditorInput fileEditorInput = new FileEditorInput((IFile) moduleResource);
				FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();
				try {

					fileDocumentProvider.connect(fileEditorInput);

					document = fileDocumentProvider.getDocument(fileEditorInput);
					if (document != null) {
						try {
							if (jumpToPCal) {
								final TLAtoPCalMapping mapping = ToolboxHandle.getCurrentSpec().getTpMapping(
										location.source() + ".tla");
								if (mapping != null) {
									final Region pCalRegion = AdapterFactory.jumptToPCal(mapping, location, document);
									if (pCalRegion != null) {
										location = pCalRegion.toLocation();
									} else {
										setStatusLineMessage("No valid TLA to PCal mapping found for current selection");
										return;
									}
								} else {
									setStatusLineMessage("No valid TLA to PCal mapping found for current selection");
									return;
								}
							}
							// we now need to convert the four coordinates of
							// the location
							// to an offset and length
							final IRegion region = AdapterFactory.locationToRegion(document, location);
							final int offset = region.getOffset();
							int length = region.getLength();

							// Hack in locationToRegion(...) which adds 1 to the
							// length, which has already been accounted for by
							// the jumpToPCal code, hence subtract.
							if (jumpToPCal) {
								length = length - 1;
							}

							// The following code sets editor to an existing
							// IEditorPart
							// (which as of June 2010 is a
							// TLAEditorAndPDFViewer) or,
							// if there is none, to a new one on the IFile
							// representing
							// the module. It then sets textEditor to the
							// ITextEditor
							// (which as of June 2010 is the TLAEditor of that
							// TLAEditorAndPDFViewer)
							// that is the TLAEditor open on the module.
							IEditorPart editor = UIHelper.openEditor(OpenSpecHandler.TLA_EDITOR_CURRENT,
									new FileEditorInput((IFile) moduleResource));

							if (editor != null) {
								ITextEditor textEditor;
								/*
								 * Try to get the text editor that contains the
								 * module. The module may be open in a multipage
								 * editor.
								 */
								if (editor instanceof ITextEditor) {
									textEditor = (ITextEditor) editor;
								} else {
									// As of June 2010, this clause is always
									// executed.
									// It may succeed in setting textEditor to
									// the TLAEditor
									// or it may return null. It should succeed
									// iff
									// the TLAEditor is the active editor in the
									// TLAEditorAndPDFViewer.
									textEditor = (ITextEditor) editor.getAdapter(ITextEditor.class);
								}

								// As of June 2010, the instanceof in following
								// if condition
								// is always true.
								if (textEditor == null && editor instanceof MultiPageEditorPart) {
									/*
									 * In this case, get all editors that are
									 * part of the multipage editor. Iterate
									 * through until a text editor is found.
									 */
									IEditorPart[] editors = ((MultiPageEditorPart) editor).findEditors(editor
											.getEditorInput());
									for (int i = 0; i < editors.length; i++) {
										if (editors[i] instanceof ITextEditor) {
											textEditor = (ITextEditor) editors[i];
										}
									}
								}

								if (textEditor != null) {
									// the text editor may not be active, so set
									// it active
									if (editor instanceof MultiPageEditorPart) {
										((MultiPageEditorPart) editor).setActiveEditor(textEditor);
									}
									// getActivePage().activate(textEditor);
									textEditor.selectAndReveal(offset, length);
								}
							}
						} catch (BadLocationException e) {
							Activator.getDefault().logError("Error accessing the specified module location", e);
						}
					}
				} catch (CoreException e1) {
					Activator.getDefault().logDebug("Error going to a module location. This is a bug.");
				} finally {
					/*
					 * The document provider is not needed. Always disconnect it
					 * to avoid a memory leak.
					 * 
					 * Keeping it connected only seems to provide
					 * synchronization of the document with file changes. That
					 * is not necessary in this context.
					 */
					fileDocumentProvider.disconnect(fileEditorInput);
				}
			}
		}
	}

	/**
	 * Calls jumpToLocation with the proper location for jumping to a SymbolNode
	 * that declares or defines a symbol. For an OpDefNode or
	 * ThmOrAssumpDefNode, this is not the same as the location returned by the
	 * node's getLocation() method for two reasons: (i) it should jump to the
	 * node's source, and (ii) that location contains the entire definition.
	 * 
	 * @param node
	 * @return
	 */
	public static void jumpToDefOrDecl(SymbolNode node) {
		Location location;
		if (node instanceof OpDefNode) {
			location = ((SyntaxTreeNode) ((OpDefNode) node).getSource().getTreeNode()).getHeirs()[0].getLocation();
		} else if (node instanceof ThmOrAssumpDefNode) {
			location = ((SyntaxTreeNode) ((ThmOrAssumpDefNode) node).getSource().getTreeNode()).getHeirs()[1]
					.getLocation();
		} else {
			location = node.getLocation();
		}
		jumpToLocation(location);
	}

	/**
	 * For all {@link TheoremNode} in the tree rooted at theoremNode, this
	 * returns the {@link TheoremNode} that is first on the line containing the
	 * caret, or null if none satisfy that criteria.
	 * 
	 * @param theoremNode
	 * @return
	 */
	public static TheoremNode getThmNodeStepWithCaret(TheoremNode theoremNode, int caretOffset, IDocument document) {
		try {
			/*
			 * Get the location of the step.
			 * 
			 * theoremNode.getTheorem() returns the node corresponding to the
			 * statement of the step (or theorem).
			 * 
			 * Return theoremNode if the caret is on any of the lines from the
			 * first line of the theoremNode to the last line of the statement
			 * of the node.
			 * 
			 * If the caret is not on any of those lines, then recursively
			 * search for a substep containing the caret.
			 */

			int nodeBeginLine = theoremNode.getLocation().beginLine();

			int nodeEndLine = theoremNode.getTheorem().getLocation().endLine();
			/*
			 * IDocument lines are 0-based and SANY Location lines are 1-based.
			 */
			int caretLine = document.getLineOfOffset(caretOffset) + 1;
			// IRegion stepRegion = AdapterFactory.locationToRegion(document,
			// stepLoc);

			if (nodeBeginLine <= caretLine && nodeEndLine >= caretLine/*
																	 * stepRegion.
																	 * getOffset
																	 * () <=
																	 * caretOffset
																	 * &&
																	 * stepRegion
																	 * .
																	 * getOffset
																	 * () +
																	 * stepRegion
																	 * .
																	 * getLength
																	 * () >=
																	 * caretOffset
																	 */) {
				return theoremNode;
			}

			/*
			 * Theorem node does not contain the caret. Recursively try to find
			 * a sub-step containing the caret if the proof contains the caret.
			 */
			ProofNode proof = theoremNode.getProof();
			if (proof != null) {
				Location proofLoc = proof.getLocation();
				if (caretLine >= proofLoc.beginLine() && caretLine <= proofLoc.endLine()) {
					if (proof instanceof NonLeafProofNode) {
						NonLeafProofNode nonLeafProof = (NonLeafProofNode) proof;
						LevelNode[] steps = nonLeafProof.getSteps();

						/*
						 * From the documentation of NonLeafProofNode, a step
						 * can be one of four types:
						 * 
						 * DefStepNode UseOrHideNode InstanceNode TheoremNode
						 * 
						 * Only TheoremNode can have a proof. Recursively
						 * compute the proof positions for those steps.
						 */
						for (int i = 0; i < steps.length; i++) {
							if (steps[i] instanceof TheoremNode) {
								TheoremNode node = getThmNodeStepWithCaret((TheoremNode) steps[i], caretOffset,
										document);
								if (node != null) {
									return node;
								}
							}
						}
					}
				}
			}

		} catch (BadLocationException e) {
			Activator.getDefault().logError("Error finding step containing caret.", e);
		}
		return null;
	}

	public static void jumpToSelection(String fileName, ITextSelection its) {
		IResource moduleResource = ResourceHelper.getResourceByModuleName(fileName.substring(0, fileName.indexOf('.')));
		if (moduleResource != null && moduleResource.exists()) {
			IEditorPart editor = UIHelper.openEditor(OpenSpecHandler.TLA_EDITOR_CURRENT, new FileEditorInput(
					(IFile) moduleResource));

			if (editor != null) {
				ITextEditor textEditor;
				/*
				 * Try to get the text editor that contains the module. The
				 * module may be open in a multipage editor.
				 */
				if (editor instanceof ITextEditor) {
					textEditor = (ITextEditor) editor;
				} else {
					textEditor = (ITextEditor) editor.getAdapter(ITextEditor.class);
				}

				if (editor instanceof MultiPageEditorPart) {
					/*
					 * In this case, get all editors that are part of the
					 * multipage editor. Iterate through until a text editor is
					 * found.
					 */
					IEditorPart[] editors = ((MultiPageEditorPart) editor).findEditors(editor.getEditorInput());
					for (int i = 0; i < editors.length; i++) {
						if (editors[i] instanceof ITextEditor) {
							textEditor = (ITextEditor) editors[i];
						}
					}
				}

				if (textEditor != null) {
					// the text editor may not be active, so set it active
					if (editor instanceof MultiPageEditorPart) {
						((MultiPageEditorPart) editor).setActiveEditor(textEditor);
					}
					// getActivePage().activate(textEditor);
					textEditor.selectAndReveal(its.getOffset(), its.getLength());
				}
			}
		}
	}

	/**
	 * This method returns a built in SWT image. This method was mostly copied
	 * directly from {@link IconAndMessageDialog}. The argument should be an
	 * icon constant defined in {@link SWT}. These constants begin with "ICON".
	 * This method returns null if the argument is not such a constant or if the
	 * platform does not define and image corresponding to that constant. I
	 * would assume you figure that one out by trial and error.
	 * 
	 * @param imageID
	 * @return
	 */
	public static Image getSWTImage(final int imageID) {

		Shell shell = getShell();
		final Display display;
		if (shell == null || shell.isDisposed()) {
			display = Display.getCurrent();
		} else {
			display = shell.getDisplay();
		}

		final Image[] image = new Image[1];
		display.syncExec(new Runnable() {
			public void run() {
				image[0] = display.getSystemImage(imageID);
			}
		});

		return image[0];

	}

	/**
	 * @return The currently active editor
	 */
	public static IEditorPart getActiveEditor() {
		return getActivePage().getActiveEditor();
	}

	/**
	 * Tries to set the given message on the workbench's status line. This is a
	 * best effort method which fails to set the status line if there is no
	 * active editor present from where the statuslinemanager can be looked up.
	 * 
	 * @param msg
	 *            The message to be shown on the status line
	 */
	public static void setStatusLineMessage(final String msg) {
		IStatusLineManager statusLineManager = null;
		ISelectionProvider selectionService = null;

		// First try to get the StatusLineManager from the IViewPart and only
		// resort back to the editor if a view isn't active right now.
		final IWorkbenchPart workbenchPart = getActiveWindow().getActivePage().getActivePart();
		if (workbenchPart instanceof IViewPart) {
			final IViewPart viewPart = (IViewPart) workbenchPart;
			statusLineManager = viewPart.getViewSite().getActionBars().getStatusLineManager();
			selectionService = viewPart.getViewSite().getSelectionProvider();
		} else if (getActiveEditor() != null) {
			final IEditorSite editorSite = getActiveEditor().getEditorSite();
			statusLineManager = editorSite.getActionBars().getStatusLineManager();
			selectionService = editorSite.getSelectionProvider();
		}

		if (statusLineManager != null && selectionService != null) {
			statusLineManager.setMessage(msg);
			selectionService.addSelectionChangedListener(new StatusLineMessageEraser(statusLineManager,
					selectionService));
		}
	}

	/**
	 * An StatusLineMessageEraser is a {@link ISelectionChangedListener} that
	 * removes a status line message.
	 */
	private static class StatusLineMessageEraser implements ISelectionChangedListener {

		private final IStatusLineManager statusLineManager;
		private final ISelectionProvider selectionService;

		private StatusLineMessageEraser(final IStatusLineManager statusLineManager, ISelectionProvider ss) {
			this.statusLineManager = statusLineManager;
			this.selectionService = ss;
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see
		 * org.eclipse.jface.viewers.ISelectionChangedListener#selectionChanged
		 * (org.eclipse.jface.viewers.SelectionChangedEvent)
		 */
		public void selectionChanged(SelectionChangedEvent event) {
			// Ideally we would verify that the current status line is indeed
			// showing the very
			// message we are about to remove, but the Eclipse API doesn't allow
			// you do get the current string.
			statusLineManager.setMessage(null);
			selectionService.removeSelectionChangedListener(this);
		}
	}

	/**
	 * Parts (Editors and Views) can be stacked if the user drags them on top of
	 * each other. This method returns true, if the given part (first parameter)
	 * and the second part (identified by its Id) are indeed stacked.
	 * 
	 * @param part
	 *            The one part (not null) for which to check if the second part
	 *            (otherId) are on the same part stack.
	 * @param otherId
	 *            The second part's id (not null).
	 * @return true iff both parts are stacked on top of each other, false
	 *         otherwise.
	 */
	public static boolean isInSameStack(final IWorkbenchPart part, final String otherId) {
		Assert.isNotNull(part);
		Assert.isNotNull(otherId);
		
		// The implementation below uses Eclipse's new UI model (e4) that is the
		// default starting with the 4.x series. It does *not* exist on any 3.x
		// release of Eclipse. Thus, if the Toolbox ever has to run on 3.x
		// again, just remove the implementation below and return false. The
		// only place where this method is used at the time of writing is to
		// prevent a stack overflow when the ModelEditor and TLCErrorView are
		// stacked. This isn't possible with 3.x anyway as Views (TLCErrorView)
		// and Editors (ModelEditor) could not be stacked upon each other (this
		// was actually an artificial restriction and missed by many). That is
		// also the very reason, why the Eclipse 3.x API does not support
		// finding out if an editor and a view are stacked
		// (IWorkbenchPage#getViewRefererences() and
		// IWorkbenchPage#getEditorReferences() are mutually exclusive).

		// Obtain the e4's part context IEclipseContext (each logical UI element
		// (parts, perspectives, application windows... have a corresponding
		// context).
		final IEclipseContext ctx = (IEclipseContext) part.getSite().getService(IEclipseContext.class);
		if (ctx == null) {
			// I don't see in which case the ctx is null, but lets be on the safe side.
			return false;
		}
		// The ctx also has the e4 UI model counterpart (MPart) to the technical
		// IWorkbenchPart instance (the UI model is a logical representation of
		// the UI state of the Toolbox).
		final MPart e4ModelPart = ctx.get(MPart.class);
		// e4 Model elements have references to their respective parents. In
		// case of our MPart/IWorkbenchPart, it is a stack if it happens to be
		// rendered in one at the moment.
		final MElementContainer<MUIElement> stack = e4ModelPart.getParent();
		if (stack == null) {
			// The part has no parent, e.g when it's not stacked
			return false;
		}
		// A MPartStack's children are the MParts currently rendered in it
		// (visible or not). Since it is the MPartStack of the IWorkbenchPart,
		// we just check if another child has the Id of the other part we are
		// interested in. If this is the case, both parts are indeed shown in
		// the same part stack on top of each other.
		final List<MUIElement> children = stack.getChildren();
		for (final MUIElement muiElement : children) {
			final String elementId = muiElement.getElementId();
			if (elementId != null && elementId.equals(otherId)) {
				return true;
			}
		}
		return false;
	}
}
