package org.lamport.tla.toolbox.util;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.NotEnabledException;
import org.eclipse.core.commands.NotHandledException;
import org.eclipse.core.commands.ParameterizedCommand;
import org.eclipse.core.commands.common.NotDefinedException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.action.IContributionItem;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartSite;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.WorkbenchException;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.IHandlerService;
import org.eclipse.ui.internal.WorkbenchWindow;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.ui.contribution.ParseStatusContributionItem;

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
     */
    public static IWorkbenchWindow openPerspectiveInWindowRight(String perspectiveId, IAdaptable input, int width)
    {
        IWorkbench workbench = Activator.getDefault().getWorkbench();
        Rectangle bounds = workbench.getActiveWorkbenchWindow().getShell().getBounds();

        IWorkbenchWindow window = openPerspectiveInNewWindow(perspectiveId, input);
        window.getShell().setBounds(bounds.x + bounds.width, bounds.y, width, bounds.height);

        activateRoorEditorOrView();
        return window;
    }

    /**
     * Tries to activates an editor or a view in the root window
     */
    private static void activateRoorEditorOrView()
    {
        // activate the editor in the root window
        IWorkbenchPage page = getRootApplicationWindow().getActivePage();
        if (page != null)
        {
            IWorkbenchPart activepart = page.getActiveEditor();
            if (activepart != null)
            {
                activepart.setFocus();
            } else {
                activepart = page.getActivePart();
                if (activepart != null) 
                {
                    activepart.setFocus();
                }
            }
        }
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
            view = getActivePage().showView(viewId);
        } catch (PartInitException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return view;
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
     * Switch current perspective
     * 
     * @param perspectiveId
     * @return
     */
    public static IWorkbenchPage switchPerspective(String perspectiveId)
    {
        IWorkbench workbench = Activator.getDefault().getWorkbench();
        IWorkbenchWindow window = workbench.getActiveWorkbenchWindow();
        try
        {
            return workbench.showPerspective(perspectiveId, window);
        } catch (WorkbenchException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        return null;
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
        IWorkbenchWindow window = getRootApplicationWindow();
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
     * Retrieves the primary root application window
     * @return the window is considered to be a root window
     */
    public static IWorkbenchWindow getRootApplicationWindow()
    {
        IWorkbenchWindow[] windows = Activator.getDefault().getWorkbench().getWorkbenchWindows();
        for (int i = 0; i < windows.length; i++)
        {
            // HACK: note this could change in future
            // we should return the smallest id, not the 1
            if (windows[i] instanceof WorkbenchWindow && ((WorkbenchWindow) windows[i]).getNumber() == 1)
            {
                return windows[i];
            }

        }
        return null;
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
     * Retrieves active shell
     * @return a parent shell of the active window
     */
    private static Shell getShell()
    {
        return getActiveWindow().getShell();
    }

    /**
     * Returns a status bar contribution.
     * This method will install the item, if it not already installed, and return the first item it finds in the status bar
     * 
     * @return ParseStatusContributionItem
     */
    public static synchronized ParseStatusContributionItem getStatusBarContributionItem()
    {
        IActionBars bars = null;
        IWorkbenchWindow window = getRootApplicationWindow();
        IWorkbenchPage page = window.getActivePage();
        if (page != null)
        {
            IWorkbenchPart part = page.getActivePart();
            if (part != null)
            {
                IWorkbenchPartSite site = part.getSite();
                if (site != null && site instanceof IViewSite)
                {
                    bars = ((IViewSite) site).getActionBars();
                } else if (site != null && site instanceof IEditorSite)
                {
                    bars = ((IEditorSite) site).getActionBars();
                }
            }
        }

        if (bars != null)
        {
            IContributionItem[] items = bars.getStatusLineManager().getItems();
            for (int i = 0; i < items.length; i++)
            {
                if (items[i] instanceof ParseStatusContributionItem)
                {
                    return (ParseStatusContributionItem) items[i];
                }
            }

            ParseStatusContributionItem parseStatusContributionItem = new ParseStatusContributionItem();
            bars.getStatusLineManager().add(parseStatusContributionItem);
            bars.updateActionBars();

            return parseStatusContributionItem;
        }
        return null;
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

}
