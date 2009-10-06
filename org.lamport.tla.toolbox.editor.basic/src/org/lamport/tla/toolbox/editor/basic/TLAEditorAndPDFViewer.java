package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.util.ResourceHelper;

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
public class TLAEditorAndPDFViewer extends FormEditor
{

    /**
     * Editor ID
     */
    public static final String ID = "org.lamport.tla.toolbox.TLAEditorAndPDFViewer";
    public static final String PDFPage_ID = "pdfPage";

    private Image rootImage = TLAEditorActivator.imageDescriptorFromPlugin(TLAEditorActivator.PLUGIN_ID,
            "/icons/root_file.gif").createImage();

    PDFViewingPage pdfViewingPage;
    IEditorInput tlaEditorInput;
    TLAEditor tlaEditor;

    protected void addPages()
    {
        try
        {
            tlaEditor = new TLAEditor();
            addPage(tlaEditor, tlaEditorInput);

            setContentDescription(tlaEditor.getContentDescription());

        } catch (PartInitException e)
        {
            e.printStackTrace();
        }
    }

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

    public void doSave(IProgressMonitor monitor)
    {
        tlaEditor.doSave(monitor);
    }

    public void doSaveAs()
    {
        tlaEditor.doSaveAs();
    }

    public boolean isSaveAsAllowed()
    {
        return tlaEditor.isSaveAsAllowed();
    }

    /**
     * Creates the pdfViewinPage and adds it to the editor if it does not exist.
     * Returns the pdfViewing page whether it previously existed or not.
     * Also sets the active page to pdfViewingPage.
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
        setActivePage(PDFPage_ID);
        return pdfViewingPage;
    }

}
