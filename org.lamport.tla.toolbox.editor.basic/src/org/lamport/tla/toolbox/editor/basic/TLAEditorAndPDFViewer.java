package org.lamport.tla.toolbox.editor.basic;

import java.io.File;
import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.INavigationLocation;
import org.eclipse.ui.INavigationLocationProvider;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditor;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * This is a multi page editor with two tabs.
 * The first tab is a module text editor.
 * The second tab is a browser that displays a pdf file
 * generated using tla2tex on the given module. This tab will only appear
 * after a pdf file has first been generated.
 * 
 * @author Daniel Ricketts
 * @version $Id$
 */
public class TLAEditorAndPDFViewer extends FormEditor implements INavigationLocationProvider, ITextEditor
{

    /**
     * Editor ID
     */
    public static final String ID = "org.lamport.tla.toolbox.editor.basic.TLAEditorAndPDFViewer";
    public static final String PDFPage_ID = "pdfPage";
    // index at which the tla module editor tab appears
    private static final int tlaEditorIndex = 0;

    private Image rootImage = TLAEditorActivator.imageDescriptorFromPlugin(TLAEditorActivator.PLUGIN_ID,
            "/icons/root_file.gif").createImage();

    PDFViewingPage pdfViewingPage;
    IEditorInput tlaEditorInput;
    TLAEditor tlaEditor;

    /* (non-Javadoc)
     * @see org.eclipse.ui.forms.editor.FormEditor#addPages()
     */
    protected void addPages()
    {
        try
        {

            // This code moves the tabs to the top of the page.
            // This makes them more obvious to the user.
            if (getContainer() instanceof CTabFolder)
            {
                ((CTabFolder) getContainer()).setTabPosition(SWT.TOP);
            }

            tlaEditor = new TLAEditor();

            addPage(tlaEditorIndex, tlaEditor, tlaEditorInput);
            setPageText(tlaEditorIndex, "TLA Module");

            setDescription();

        } catch (PartInitException e)
        {
            e.printStackTrace();
        }
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.forms.editor.FormEditor#init(org.eclipse.ui.IEditorSite, org.eclipse.ui.IEditorInput)
     */
    public void init(IEditorSite site, IEditorInput input) throws PartInitException
    {

        tlaEditorInput = input;
        if (input instanceof FileEditorInput)
        {
            FileEditorInput finput = (FileEditorInput) input;
            if (finput != null)
            {
                if (ResourceHelper.isModule(finput.getFile()))
                {
                    this.setPartName(finput.getFile().getName());
                }

                if (ResourceHelper.isRoot(finput.getFile()))
                {
                    setTitleImage(rootImage);
                }
            }
        }
        super.init(site, input);
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.part.EditorPart#doSave(org.eclipse.core.runtime.IProgressMonitor)
     */
    public void doSave(IProgressMonitor monitor)
    {
        tlaEditor.doSave(monitor);
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.part.EditorPart#doSaveAs()
     */
    public void doSaveAs()
    {

        IFile file = ((FileEditorInput) getEditorInput()).getFile();
        Shell shell = UIHelper.getShellProvider().getShell();

        // TODO fix this?
        IPath specRootPrefix = new Path(ResourceHelper.getParentDirName(ToolboxHandle.getRootModule()));

        FileDialog saveAsDialog = null;
        while (true)
        {
            // construct the dialog
            // should this be replaced by a dialog showing the logical view of the FS?
            saveAsDialog = new FileDialog(shell, SWT.SAVE);
            saveAsDialog.setOverwrite(true);
            saveAsDialog.setText("Select the new filename...");
            saveAsDialog.setFilterExtensions(new String[] { "*.tla" });
            saveAsDialog.setFilterNames(new String[] { "TLA+ Files" });
            saveAsDialog.setFilterPath(ResourceHelper.getParentDirName(file));
            String result = saveAsDialog.open();
            saveAsDialog = null;
            // no cancellation
            if (result != null)
            {
                IPath newPath = new Path(result);
                // check whether the file is in the same directory as the root module
                if (!specRootPrefix.isPrefixOf(newPath))
                {
                    MessageDialog.openError(shell, "Wrong location selected",
                            "The provided filename must point to the same directory as the specification root file");
                    continue;
                }

                // fix the extension
                if (!"tla".equals(newPath.getFileExtension()))
                {
                    newPath = newPath.addFileExtension("tla");
                }

                File newFile = newPath.toFile();
                if (newFile.exists())
                {
                    boolean confirmOverwrite = MessageDialog.openQuestion(shell, "Overwrite file?",
                            "The provided filename already exists. The existing file will be overwritten.\nDo you want to overwrite the file "
                                    + newPath.toOSString() + "?");
                    if (!confirmOverwrite)
                    {
                        continue;
                    }

                    // overwriting existing file file exists
                } else
                {
                    // file does not exist
                    // create the empty file
                    boolean newFileCreated = false;
                    try
                    {
                        newFileCreated = newFile.createNewFile();
                    } catch (IOException e)
                    {
                        // do nothing, since we react on the newFileCreated being false
                    }
                    if (!newFileCreated)
                    {
                        MessageDialog.openError(shell, "Error saving a file", "File could not be created");
                        break;
                    }
                }

                // create a link to a file
                IFile newResource = ResourceHelper.getLinkedFile(file.getProject(), newPath.toOSString());

                // new editor input
                IEditorInput newInput = new FileEditorInput(newResource);

                // System.out.println("TODO: Save " + file.getLocation().toOSString() + " as " + newPath);

                // get the document provider
                IDocumentProvider provider = tlaEditor.getDocumentProvider();
                boolean saveAsSuccess = false;
                try
                {
                    // notify
                    provider.aboutToChange(newInput);
                    // perform the save
                    provider.saveDocument(new NullProgressMonitor(), newInput, provider.getDocument(getEditorInput()),
                            true);
                    saveAsSuccess = true;
                } catch (CoreException x)
                {
                    MessageDialog.openError(shell, "Error saving a file", "File could not be created");
                } finally
                {
                    // notify
                    provider.changed(newInput);
                    if (saveAsSuccess)
                    {
                        // change the input
                        // alternatively, open another editor with the new resource?
                        setInput(newInput);
                        tlaEditor.setInput(newInput);
                        if (newInput instanceof FileEditorInput)
                        {
                            FileEditorInput fin = (FileEditorInput) newInput;
                            setPartName(fin.getFile().getName());
                            setDescription();
                        }
                    }
                }
                // break out on save
                break;
            } else
            {
                // break out on cancel of the dialog
                break;
            }
        }
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.part.EditorPart#isSaveAsAllowed()
     */
    public boolean isSaveAsAllowed()
    {
        return tlaEditor.isSaveAsAllowed();
    }


    
	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocationProvider#createEmptyNavigationLocation()
	 */
	public INavigationLocation createEmptyNavigationLocation() {
		return tlaEditor.createEmptyNavigationLocation();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocationProvider#createNavigationLocation()
	 */
	public INavigationLocation createNavigationLocation() {
		return tlaEditor.createNavigationLocation();
	}

	/**
     * Creates the pdfViewinPage and adds it to the editor if it does not exist.
     * Returns the pdfViewing page whether it previously existed or not.
     * @return
     */
    public PDFViewingPage getPDFViewingPage()
    {
        if (pdfViewingPage == null)
        {
            pdfViewingPage = new PDFViewingPage(this, PDFPage_ID, "PDF Viewer");
            try
            {
                addPage(pdfViewingPage);
            } catch (PartInitException e)
            {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
        // setActivePage(PDFPage_ID);
        return pdfViewingPage;
    }

    public TLAEditor getTLAEditor()
    {
        return tlaEditor;
    }

    /**
     * Sets the text that appears above the text viewer.
     * Currently, this is the full file path.
     */
    private void setDescription()
    {
        IEditorInput input = getEditorInput();
        if (input != null)
        {
            if (input instanceof FileEditorInput)
            {
                FileEditorInput fin = (FileEditorInput) input;
                setContentDescription(fin.getPath().toOSString());
            } else
            {
                setContentDescription(input.getName());
            }
        }
    }
    
    /**
     * Sets the TLA module editor as the active
     * tab for this editor. Does not necessarily make
     * this multi-page editor the active editor.
     */
    public void setTLAEditorActive()
    {
        setActivePage(tlaEditorIndex);
    }


    /* (non-Javadoc)
     * @see org.eclipse.ui.texteditor.ITextEditor#getDocumentProvider()
     */
    public IDocumentProvider getDocumentProvider() {
		return tlaEditor.getDocumentProvider();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.texteditor.ITextEditor#isEditable()
	 */
	public boolean isEditable() {
		return tlaEditor.isEditable();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.texteditor.ITextEditor#doRevertToSaved()
	 */
	public void doRevertToSaved() {
		tlaEditor.doRevertToSaved();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.texteditor.ITextEditor#setAction(java.lang.String, org.eclipse.jface.action.IAction)
	 */
	public void setAction(String actionID, IAction action) {
		tlaEditor.setAction(actionID, action);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.texteditor.ITextEditor#getAction(java.lang.String)
	 */
	public IAction getAction(String actionId) {
		return tlaEditor.getAction(actionId);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.texteditor.ITextEditor#setActionActivationCode(java.lang.String, char, int, int)
	 */
	public void setActionActivationCode(String actionId,
			char activationCharacter, int activationKeyCode,
			int activationStateMask) {
		tlaEditor.setActionActivationCode(actionId, activationCharacter, activationKeyCode, activationStateMask);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.texteditor.ITextEditor#removeActionActivationCode(java.lang.String)
	 */
	public void removeActionActivationCode(String actionId) {
		tlaEditor.removeActionActivationCode(actionId);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.texteditor.ITextEditor#showsHighlightRangeOnly()
	 */
	public boolean showsHighlightRangeOnly() {
		return tlaEditor.showsHighlightRangeOnly();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.texteditor.ITextEditor#showHighlightRangeOnly(boolean)
	 */
	public void showHighlightRangeOnly(boolean showHighlightRangeOnly) {
		tlaEditor.showHighlightRangeOnly(showHighlightRangeOnly);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.texteditor.ITextEditor#setHighlightRange(int, int, boolean)
	 */
	public void setHighlightRange(int offset, int length, boolean moveCursor) {
		tlaEditor.setHighlightRange(offset, length, moveCursor);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.texteditor.ITextEditor#getHighlightRange()
	 */
	public IRegion getHighlightRange() {
		return tlaEditor.getHighlightRange();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.texteditor.ITextEditor#resetHighlightRange()
	 */
	public void resetHighlightRange() {
		tlaEditor.resetHighlightRange();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.texteditor.ITextEditor#getSelectionProvider()
	 */
	public ISelectionProvider getSelectionProvider() {
		return tlaEditor.getSelectionProvider();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.texteditor.ITextEditor#selectAndReveal(int, int)
	 */
	public void selectAndReveal(int offset, int length) {
		tlaEditor.selectAndReveal(offset, length);
	}

}
