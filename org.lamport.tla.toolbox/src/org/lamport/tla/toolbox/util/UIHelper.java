package org.lamport.tla.toolbox.util;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.NotEnabledException;
import org.eclipse.core.commands.NotHandledException;
import org.eclipse.core.commands.ParameterizedCommand;
import org.eclipse.core.commands.common.NotDefinedException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.window.IShellProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.BusyIndicator;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.eclipse.ui.IPerspectiveListener;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.WorkbenchException;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.IHandlerService;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.ui.perspective.InitialPerspective;
import org.lamport.tla.toolbox.ui.property.GenericSelectionProvider;
import org.lamport.tla.toolbox.ui.view.ToolboxWelcomeView;

/**
 * A Helper for handling the RCP Objects like windows, editors and views
 * @version $Id$
 * @author zambrovski
 */
public class UIHelper
{

    /**
     * Closes all windows with a perspective
     * 
     * @param perspectiveId
     *            a perspective Id pointing the perspective
     */
    public static void closeWindow(String perspectiveId)
    {
        IWorkbench workbench = Activator.getDefault().getWorkbench();
        // hide intro
        if (InitialPerspective.ID.equals(perspectiveId))
        {
            workbench.getIntroManager().closeIntro(workbench.getIntroManager().getIntro());
        }

        IWorkbenchWindow[] windows = workbench.getWorkbenchWindows();

        // closing the perspective opened in a window
        for (int i = 0; i < windows.length; i++)
        {
            IWorkbenchPage page = windows[i].getActivePage();
            if (page != null && page.getPerspective() != null && perspectiveId.equals(page.getPerspective().getId()))
            {
                windows[i].close();
            }
        }
    }

    /**
     * Opens the perspective in a new window on the right of the original window 
     * @param perspectiveId
     * @param input
     * @param width - width of new window
     * @return
     * @deprecated
     */
    public static IWorkbenchWindow openPerspectiveInWindowRight(String perspectiveId, IAdaptable input, int width)
    {
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
    public static IWorkbenchWindow openPerspectiveInNewWindow(String perspectiveId, IAdaptable input)
    {
        IWorkbench workbench = Activator.getDefault().getWorkbench();
        IWorkbenchWindow window = null;
        try
        {
            // avoids flicking, from implementation above
            window = workbench.openWorkbenchWindow(perspectiveId, input);

            // show intro
            if (InitialPerspective.ID.equals(perspectiveId) && workbench.getIntroManager().hasIntro())
            {
                // IIntroPart intro =
                workbench.getIntroManager().showIntro(window, true);
            }

        } catch (WorkbenchException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return window;
    }

    /**
     * Opens a view
     * @param viewId
     * @return the reference to the view
     */
    public static IViewPart openView(String viewId)
    {
        IViewPart view = null;
        try
        {
            IWorkbenchPage activePage = getActivePage();
            if (activePage != null)
            {
                view = activePage.showView(viewId);
            }
        } catch (PartInitException e)
        {
            Activator.logError("Error opening a view " + viewId, e);
        }
        return view;
    }

    /**
     * Find a view if on the page
     * @param viewId
     * @return
     */
    public static IViewPart findView(String viewId)
    {
        IViewPart view = null;
        IWorkbenchPage activePage = getActivePage();
        if (activePage != null)
        {
            view = activePage.findView(viewId);
        }
        return view;
    }

    /**
     * Checks weather the view is shown 
     * @param id view Id
     * @return
     */
    public static boolean isViewShown(String id)
    {
        return (getActivePage().findView(id) == null);

    }

    /**
     * Hides a view
     * @param id Id of the view to hide
     */
    public static void hideView(String id)
    {
        IViewPart findView = getActivePage().findView(id);
        if (findView != null)
        {
            getActivePage().hideView(findView);
        }
    }

    /**
     * Returns the perspective to its initial layout
     * @param perspectiveId
     */
    public static void revertPerspecive(String perspectiveId)
    {
        IWorkbench workbench = Activator.getDefault().getWorkbench();
        IPerspectiveDescriptor descriptor = workbench.getPerspectiveRegistry().findPerspectiveWithId(perspectiveId);
        workbench.getPerspectiveRegistry().revertPerspective(descriptor);
    }

    /**
     * Attaches the perspective listener to active window 
     * 
     * @param listener
     */
    public static void addPerspectiveListener(IPerspectiveListener listener)
    {
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
    public static IWorkbenchPage switchPerspective(String perspectiveId)
    {
        Assert.isNotNull(perspectiveId, "PerspectiveId is null");
        IWorkbench workbench = PlatformUI.getWorkbench();
        IWorkbenchWindow window = getActiveWindow();
        Assert.isNotNull(workbench, "Workbench is null");
        Assert.isNotNull(window, "Window is null");
        try
        {
            IWorkbenchPage page = workbench.showPerspective(perspectiveId, window);

            // show intro
            if (InitialPerspective.ID.equals(perspectiveId) && workbench.getIntroManager().hasIntro())
            {
                page.resetPerspective();
                // We are no longer showing the Intro view. The following will probably
                // be replaced by something that shows the view we want. 09 Oct 2009
                // workbench.getIntroManager().showIntro(window, false);
                openView(ToolboxWelcomeView.ID);

            }

            return page;
        } catch (WorkbenchException e)
        {
            Activator.logError("Error switching a perspective to " + perspectiveId, e);
        }

        return null;
    }

    /**
     * Retrieves the id of currently selected perspective
     * @return
     */
    public static String getActivePerspectiveId()
    {
        return UIHelper.getActivePage().getPerspective().getId();
    }

    /**
     * Convenience method to reduce client dependencies
     * @param editorId
     * @param file
     * @return
     */
    public static IEditorPart openEditor(String editorId, IFile file)
    {
        return openEditor(editorId, new FileEditorInput(file));
    }

    /**
     * Opens an editor in current workbench window
     * 
     * @param editorId
     * @param input
     * @return the created or reopened IEditorPart
     */
    public static IEditorPart openEditor(String editorId, IEditorInput input)
    {
        IWorkbenchWindow window = getActiveWindow();
        IEditorPart editorPart = null;
        try
        {
            editorPart = window.getActivePage().openEditor(input, editorId);
        } catch (PartInitException e)
        {
            e.printStackTrace();
        }

        return editorPart;
    }

    /**
     * Retrieves active window
     * 
     * @return
     */
    public static IWorkbenchWindow getActiveWindow()
    {
        return PlatformUI.getWorkbench().getActiveWorkbenchWindow();
    }

    /**
     * Retrieves active page
     * 
     * @return
     */
    public static IWorkbenchPage getActivePage()
    {
        IWorkbenchWindow window = getActiveWindow();
        if (window == null)
        {
            // try to get an not null window
            IWorkbenchWindow[] workbenchWindows = PlatformUI.getWorkbench().getWorkbenchWindows();
            for (int i = 0; i < workbenchWindows.length; i++)
            {
                if (workbenchWindows[i] != null)
                {
                    return workbenchWindows[i].getActivePage();
                }
            }
            return null;
        }
        return window.getActivePage();
    }

    /**
     * Retrieves the list of resources opened in editor
     * 
     * @return an array of paths of opened resources
     */
    public static String[] getOpenedResources()
    {
        IEditorReference[] references = getActivePage().getEditorReferences();
        String[] openedResources = new String[references.length];

        for (int i = 0; i < references.length; i++)
        {
            openedResources[i] = references[i].getContentDescription();
        }

        return openedResources;
    }

    /**
     * Runs a command with parameters
     * 
     * @param commandId
     * @param parameters
     * @return
     */
    public static Object runCommand(String commandId, HashMap parameters)
    {
        IHandlerService handlerService = (IHandlerService) UIHelper.getActiveWindow().getService(IHandlerService.class);
        ICommandService commandService = (ICommandService) UIHelper.getActiveWindow().getService(ICommandService.class);
        try
        {
            Command command = commandService.getCommand(commandId);
            ParameterizedCommand pCommand = ParameterizedCommand.generateCommand(command, parameters);
            return handlerService.executeCommand(pCommand, null);
        } catch (NotDefinedException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (NotEnabledException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (NotHandledException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (ExecutionException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        return null;
    }

    /**
     * 
     */
    public static List checkOpenResources(String title, String message)
    {
        List dirtyEditors = new LinkedList();
        IEditorReference[] references = UIHelper.getActivePage().getEditorReferences();
        if (references != null)
        {
            for (int i = 0; i < references.length; i++)
            {
                if (references[i].isDirty())
                {
                    dirtyEditors.add(references[i]);
                }
            }
        }

        if (dirtyEditors.size() > 0)
        {
            boolean saveFiles = MessageDialog.openQuestion(getShell(), title, message);
            if (saveFiles)
            {
                // TODO provide a way to select what to save and what to drop
                // TODO provide a way to cancel
                return dirtyEditors;
            }
        }

        return new LinkedList();
    }

    /**
     * If there are unsaved modules open, this prompts the user
     * to save the modules with an OK/Cancel dialog. If the user
     * selects OK, this saves the modules before returning, other wise it does not.
     * 
     * @return false if a dialog is opened and the user selects cancel or the user closes
     * the dialog without pressing OK or cancel, true otherwise
     */
    public static boolean promptUserForDirtyModules()
    {
        final List dirtyEditors = new LinkedList();
        IEditorReference[] references = UIHelper.getActivePage().getEditorReferences();
        if (references != null)
        {
            for (int i = 0; i < references.length; i++)
            {
                try
                {
                    if (references[i].isDirty() && references[i].getEditorInput().getName().endsWith(".tla"))
                    {
                        dirtyEditors.add(references[i]);
                    }
                } catch (PartInitException e)
                {
                    Activator.logError("Error getting unsaved resources.", e);
                }
            }
        }

        if (dirtyEditors.size() > 0)
        {

            // opens a OK/cancel dialog
            boolean saveFiles = MessageDialog.openConfirm(getShell(), "Modified resources",
                    "Some resources are modified.\nDo you want to save the modified resources?");

            if (saveFiles)
            {
                // User selected OK
                runUISync(new Runnable() {

                    public void run()
                    {
                        // save modified resources
                        Iterator it = dirtyEditors.iterator();
                        while (it.hasNext())
                        {
                            Object next = it.next();
                            if (next instanceof IEditorReference)
                            {
                                IEditorReference reference = (IEditorReference) next;
                                IEditorPart editor = reference.getEditor(false);
                                if (editor != null)
                                {
                                    editor.doSave(new NullProgressMonitor());
                                }
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
    public static FileDialog getFileDialog(Shell shell)
    {
        FileDialog openFileDialog = null;

        // platform dependent code
        // on mac, we need a Save dialog in order to allow
        // the user to type in a file name as well as select one
        // on other platforms, an open dialog is sufficient
        if (Platform.getOS().equals(Platform.OS_MACOSX))
        {
            // Mac
            openFileDialog = new FileDialog(shell, SWT.SAVE);
            // we dont want the system to prompt the user
            // to overwrite the existing file simply because
            // this is called a "save" dialog
            // overwriting makes no sense in this context
            openFileDialog.setOverwrite(false);
        } else
        {
            // all other operating systems
            openFileDialog = new FileDialog(shell, SWT.OPEN);
        }

        return openFileDialog;
    }

    /**
     * Retrieves active shell
     * @return a parent shell of the active window
     */
    private static Shell getShell()
    {
        return getActiveWindow().getShell();
    }

    /**
     * Runs a task in synchronous UI thread 
     * @param task
     */
    public static void runUISync(Runnable task)
    {
        Display display = Display.getCurrent();
        if (display == null)
        {
            display = Display.getDefault();
        }
        display.syncExec(task);
    }

    /**
     * Runs a task in asynchronous UI thread 
     * @param task
     */
    public static void runUIAsync(Runnable task)
    {
        Display display = Display.getCurrent();
        if (display == null)
        {
            display = Display.getDefault();
        }
        display.asyncExec(task);
    }

    /**
     * Determines if given perspective is shown
     * @param id
     * @return true if the perspective with current id is shown, false otherwise
     */
    public static boolean isPerspectiveShown(String perspectiveId)
    {
        if (perspectiveId == null || perspectiveId.equals(""))
        {
            return false;
        }
        IWorkbenchWindow[] workbenchWindows = PlatformUI.getWorkbench().getWorkbenchWindows();
        for (int i = 0; i < workbenchWindows.length; i++)
        {
            IPerspectiveDescriptor[] openPerspectives = workbenchWindows[i].getActivePage().getOpenPerspectives();
            for (int j = 0; j < openPerspectives.length; j++)
            {
                if (perspectiveId.equals(openPerspectives[j].getId()))
                {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Registers a control to the context
     * This can only be used within the plug-in org.lamport.tla.toolbox
     * @param control control to register 
     * @param localContext the context id relative to org.lamport.tla.toolbox plug-in ID 
     * <br>
     * Note: there should be a corresponding context ID defined in the contexts.xml defining the context for current ID. 
     */
    public static void setHelp(Control control, String localContext)
    {
        PlatformUI.getWorkbench().getHelpSystem().setHelp(control, Activator.PLUGIN_ID + "." + localContext);
    }

    /**
     * Convenience method
     * @see {@link Activator#imageDescriptorFromPlugin(String, String)}
     */
    public static ImageDescriptor imageDescriptor(String imageFilePath)
    {
        return Activator.imageDescriptorFromPlugin(Activator.PLUGIN_ID, imageFilePath);
    }

    /**
     * Retrieves a shell provider of currently active shell
     * @return
     */
    public static IShellProvider getShellProvider()
    {
        return new IShellProvider() {

            public Shell getShell()
            {
                return UIHelper.getShell();
            }
        };
    }

    /**
     * Retrieves the selection provider for files in the active editor 
     * @return
     */
    public static ISelectionProvider getActiveEditorFileSelectionProvider()
    {
        return new GenericSelectionProvider() {

            public ISelection getSelection()
            {
                IEditorInput input = getActivePage().getActiveEditor().getEditorInput();
                if (input instanceof FileEditorInput)
                {
                    IFile resource = ((FileEditorInput) input).getFile();
                    return new StructuredSelection(resource);
                }
                return null;
            }

            public void setSelection(ISelection selection)
            {
                throw new UnsupportedOperationException("This selection provider is read-only");
            }

        };
    }

    /**
     * Retrieves the control from the viewer
     */
    public static Control getWidget(Object control)
    {
        if (control instanceof Viewer)
        {
            return ((Viewer) control).getControl();
        } else if (control instanceof Text)
        {
            return (Text) control;
        } else if (control instanceof Button)
        {
            return (Control) control;
        }

        return null;
    }

    public static void showDynamicHelp()
    {
        // This may take a while, so use the busy indicator
        BusyIndicator.showWhile(null, new Runnable() {
            public void run()
            {
                getActiveWindow().getWorkbench().getHelpSystem().displayDynamicHelp();
                // the following ensure that the help view receives focus
                // prior to adding this, it would not receive focus if
                // it was opened into a folder or was already
                // open in a folder in which another part had focus
                IViewPart helpView = findView("org.eclipse.help.ui.HelpView");
                if (helpView != null && getActiveWindow() != null && getActiveWindow().getActivePage() != null)
                {
                    getActiveWindow().getActivePage().activate(helpView);
                }
            }
        });
    }

}
