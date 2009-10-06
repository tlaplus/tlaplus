package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.swt.SWT;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.editor.FormPage;

/**
 * Contains a browser for viewing pdf files. Used as a page in
 * TLAEditorAndPDFViewer.
 * 
 * @author Daniel Ricketts
 * @version $Id$
 */
public class PDFViewingPage extends FormPage
{

    Browser browser;
    Composite body;

    public PDFViewingPage(FormEditor editor, String id, String title)
    {
        super(editor, id, title);
    }

    protected void createFormContent(IManagedForm managedForm)
    {
        body = managedForm.getForm().getBody();
        body.setLayout(new FillLayout());
        browser = new Browser(body, SWT.NONE);

        super.createFormContent(managedForm);
    }

    public Browser getBrowser()
    {
        return browser;
    }

}
