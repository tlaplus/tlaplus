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
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
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
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.handlers.IHandlerService;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.part.MultiPageEditorPart;
import org.eclipse.ui.texteditor.ITextEditor;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.ui.handler.OpenSpecHandler;
import org.lamport.tla.toolbox.ui.perspective.InitialPerspective;
import org.lamport.tla.toolbox.ui.property.GenericSelectionProvider;
import org.lamport.tla.toolbox.ui.view.ToolboxWelcomeView;

import tla2sany.semantic.LevelNode;
import tla2sany.semantic.NonLeafProofNode;
import tla2sany.semantic.ProofNode;
import tla2sany.semantic.TheoremNode;
import tla2sany.semantic.ThmOrAssumpDefNode;
import tla2sany.st.Location;

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
     * Note added by LL:
     * In case you don't have time to read the extensive comment above
     * written by Simon, here is my attempt at a condensed version.  This
     * method takes a commandId, which was registered in the plugin.xml file
     * as a command for the org.eclipse.ui.commands extension, 
     * as the name of a command, and invokes the Eclipse magic that calls
     * the execute(...) method of the Handler class for the handler that was  
     * associated with that command by adding it to the extension org.eclipse.ui.handlers
     * (in some plugin.xml file) and giving it the command's Id.  (I'm surprised
     * that Eclipse was able to do that with so few levels of indirection.)
     * 
     * The parameters argument seems to be used as follows for passing arguments
     * to the execute(e) command. The caller of UIHelper.java packages the
     * parameters as a HashMap by executing
     * 
     *    HashMap parameters = new HashMap();
     *    parameters.put(ParameterNameAsAString, parameterValue);
     *    ...
     *    
     * The execute(event) command fetches the parameters by executing
     * 
     *    ... = event.getParameter((String) ParameterNameAsString);
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
            // since this could be a save as dialog trying
            // to act as an open dialog, the default will be
            // to not prompt the user to overwrite a file because
            // that would not make any sense in an open file dialog.
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

    /**
     * Reveals and highlights the given location in a TLA editor. Opens
     * an editor on the module if an editor is not already open on it.
     * 
     * @param location
     */
    public static void jumpToLocation(Location location)
    {
        if (location != null)
        {
            // the source of a location is the module name
            IResource moduleResource = ResourceHelper.getResourceByModuleName(location.source());
            if (moduleResource != null && moduleResource.exists())
            {
                /*
                 * Now, retrieve a representation of the resource
                 * as a document. To do this, we use a FileDocumentProvider.
                 * 
                 * We disconnect the document provider in the finally block
                 * for the following try block in order to avoid a memory leak.
                 */
                IDocument document = null;

                // since we know that the editor uses file based editor representation
                FileEditorInput fileEditorInput = new FileEditorInput((IFile) moduleResource);
                FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();
                try
                {

                    fileDocumentProvider.connect(fileEditorInput);

                    document = fileDocumentProvider.getDocument(fileEditorInput);
                    if (document != null)
                    {
                        try
                        {
                            // we now need to convert the four coordinates of the location
                            // to an offset and length

                            /*
                             * The following was commented out by DR on May 6, 2010. It originally was required
                             * to compensate for a bug in the reporting of locations by SANY. SANY
                             * was reporting multiline locations as a bounding box instead of the
                             * actual begin line, begin column, end line, end column. This has
                             * been fixed, so the commented out code can be simplified to what follows it.
                             */
                            // // find the two lines in the document
                            // IRegion beginLineRegion = document.getLineInformation(location.beginLine() - 1);
                            // IRegion endLineRegion = document.getLineInformation(location.endLine() - 1);
                            //
                            // // get the text representation of the lines
                            // String textBeginLine = document.get(beginLineRegion.getOffset(), beginLineRegion
                            // .getLength());
                            // String textEndLine = document.get(endLineRegion.getOffset(), endLineRegion.getLength());
                            //
                            // // the Math.min is necessary because sometimes the end column
                            // // is greater than the length of the end line, so if Math.min
                            // // were not called in such a situation, extra lines would be
                            // // highlighted
                            // int offset = beginLineRegion.getOffset()
                            // + Math.min(textBeginLine.length(), location.beginColumn() - 1);
                            // int length = endLineRegion.getOffset()
                            // + Math.min(textEndLine.length(), location.endColumn()) - offset;

                            /*
                             * This is the new code for converting to an offset and length.
                             */
                            IRegion region = AdapterFactory.locationToRegion(document, location);
                            int offset = region.getOffset();
                            int length = region.getLength();

                            IEditorPart editor = UIHelper.openEditor(OpenSpecHandler.TLA_EDITOR_CURRENT,
                                    new FileEditorInput((IFile) moduleResource));

                            if (editor != null)
                            {
                                ITextEditor textEditor;
                                /*
                                 * Try to get the text editor that contains the module.
                                 * The module may be open in a multipage editor.
                                 */
                                if (editor instanceof ITextEditor)
                                {
                                    textEditor = (ITextEditor) editor;
                                } else
                                {
                                    textEditor = (ITextEditor) editor.getAdapter(ITextEditor.class);
                                }

                                if (editor instanceof MultiPageEditorPart)
                                {
                                    /*
                                     * In this case, get all editors that are
                                     * part of the multipage editor. Iterate through
                                     * until a text editor is found.
                                     */
                                    IEditorPart[] editors = ((MultiPageEditorPart) editor).findEditors(editor
                                            .getEditorInput());
                                    for (int i = 0; i < editors.length; i++)
                                    {
                                        if (editors[i] instanceof ITextEditor)
                                        {
                                            textEditor = (ITextEditor) editors[i];
                                        }
                                    }
                                }

                                if (textEditor != null)
                                {
                                    // the text editor may not be active, so set it active
                                    if (editor instanceof MultiPageEditorPart)
                                    {
                                        ((MultiPageEditorPart) editor).setActiveEditor(textEditor);
                                    }
                                    // getActivePage().activate(textEditor);
                                    textEditor.selectAndReveal(offset, length);
                                }
                            }
                        } catch (BadLocationException e)
                        {
                            Activator.logError("Error accessing the specified module location", e);
                        }
                    }
                } catch (CoreException e1)
                {
                    Activator.logDebug("Error going to a module location. This is a bug.");
                } finally
                {
                    /*
                     * The document provider is not needed. Always disconnect it to avoid a memory leak.
                     * 
                     * Keeping it connected only seems to provide synchronization of
                     * the document with file changes. That is not necessary in this context.
                     */
                    fileDocumentProvider.disconnect(fileEditorInput);
                }
            }
        }
    }

    /**
     * For all {@link TheoremNode} in the tree rooted at theoremNode,
     * this returns the {@link TheoremNode} that is first on the line
     * containing the caret, or null if none satisfy that criteria.
     * 
     * @param theoremNode
     * @return
     */
    public static TheoremNode getThmNodeStepWithCaret(TheoremNode theoremNode, int caretOffset, IDocument document)
    {
        try
        {
            /*
             * Get the location of the step.
             * 
             * theoremNode.getTheorem() returns the node
             * corresponding to the statement of the step (or theorem).
             * 
             * Return theoremNode if the caret is on any of the lines
             * from the first line of the theoremNode to the
             * last line of the statement of the node.
             * 
             * If the caret is not on any of those lines, then
             * recursively search for a substep containing the caret.
             */

            int nodeBeginLine = theoremNode.getLocation().beginLine();

            int nodeEndLine = theoremNode.getTheorem().getLocation().endLine();
            /*
             * IDocument lines are 0-based and SANY Location lines
             * are 1-based.
             */
            int caretLine = document.getLineOfOffset(caretOffset) + 1;
            // IRegion stepRegion = AdapterFactory.locationToRegion(document, stepLoc);

            if (nodeBeginLine <= caretLine && nodeEndLine >= caretLine/*stepRegion.getOffset() <= caretOffset && stepRegion.getOffset() + stepRegion.getLength() >= caretOffset*/)
            {
                return theoremNode;
            }

            /*
             * Theorem node does not contain the caret.
             * Recursively try to find a sub-step containing
             * the caret if the proof contains the caret.
             */
            ProofNode proof = theoremNode.getProof();
            if (proof != null)
            {
                Location proofLoc = proof.getLocation();
                if (caretLine >= proofLoc.beginLine() && caretLine <= proofLoc.endLine())
                {
                    if (proof instanceof NonLeafProofNode)
                    {
                        NonLeafProofNode nonLeafProof = (NonLeafProofNode) proof;
                        LevelNode[] steps = nonLeafProof.getSteps();

                        /*
                         * From the documentation of NonLeafProofNode,
                         * a step can be one of four types:
                         * 
                         * DefStepNode
                         * UseOrHideNode
                         * InstanceNode
                         * TheoremNode
                         * 
                         * Only TheoremNode can have a proof. Recursively compute
                         * the proof positions for those steps.
                         */
                        for (int i = 0; i < steps.length; i++)
                        {
                            if (steps[i] instanceof TheoremNode)
                            {
                                TheoremNode node = getThmNodeStepWithCaret((TheoremNode) steps[i], caretOffset,
                                        document);
                                if (node != null)
                                {
                                    return node;
                                }
                            }
                        }
                    }
                }
            }

        } catch (BadLocationException e)
        {
            Activator.logError("Error finding step containing caret.", e);
        }
        return null;
    }

    public static void jumpToSelection(String fileName, ITextSelection its)
    {
        IResource moduleResource = ResourceHelper.getResourceByModuleName(fileName.substring(0, fileName.indexOf('.')));
        if (moduleResource != null && moduleResource.exists())
        {
            IEditorPart editor = UIHelper.openEditor(OpenSpecHandler.TLA_EDITOR_CURRENT, new FileEditorInput(
                    (IFile) moduleResource));

            if (editor != null)
            {
                ITextEditor textEditor;
                /*
                 * Try to get the text editor that contains the module.
                 * The module may be open in a multipage editor.
                 */
                if (editor instanceof ITextEditor)
                {
                    textEditor = (ITextEditor) editor;
                } else
                {
                    textEditor = (ITextEditor) editor.getAdapter(ITextEditor.class);
                }

                if (editor instanceof MultiPageEditorPart)
                {
                    /*
                     * In this case, get all editors that are
                     * part of the multipage editor. Iterate through
                     * until a text editor is found.
                     */
                    IEditorPart[] editors = ((MultiPageEditorPart) editor).findEditors(editor.getEditorInput());
                    for (int i = 0; i < editors.length; i++)
                    {
                        if (editors[i] instanceof ITextEditor)
                        {
                            textEditor = (ITextEditor) editors[i];
                        }
                    }
                }

                if (textEditor != null)
                {
                    // the text editor may not be active, so set it active
                    if (editor instanceof MultiPageEditorPart)
                    {
                        ((MultiPageEditorPart) editor).setActiveEditor(textEditor);
                    }
                    // getActivePage().activate(textEditor);
                    textEditor.selectAndReveal(its.getOffset(), its.getLength());
                }
            }
        }
    }

}
