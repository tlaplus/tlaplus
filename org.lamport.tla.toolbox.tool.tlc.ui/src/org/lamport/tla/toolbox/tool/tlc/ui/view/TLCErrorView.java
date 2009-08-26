package org.lamport.tla.toolbox.tool.tlc.ui.view;

import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.ViewPart;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCError;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Error representation
 * @author Simon Zambrovski
 * @version $Id$
 * This is the view of the error description.  
 */

public class TLCErrorView extends ViewPart
{
    public static final String ID = "toolbox.tool.tlc.view.TLCErrorView";
    private static final IDocument EMPTY_DOCUMENT = new Document("No error information");

    private SourceViewer detailViewer;
    private List problems;

    /**
     * Creates the layout and fill it with data 
     */
    public void createPartControl(Composite parent)
    {
        SashForm sashForm = new SashForm(parent, SWT.VERTICAL);

        detailViewer = FormHelper.createOutputViewer(sashForm, SWT.V_SCROLL | SWT.MULTI | SWT.BORDER);
        detailViewer.setDocument(EMPTY_DOCUMENT);

        UIHelper.setHelp(parent, "TLCErrorView");
    }

    public void clear()
    {
        detailViewer.setDocument(EMPTY_DOCUMENT);
        TraceExplorer traceExplorer = (TraceExplorer) UIHelper.findView(TraceExplorer.ID);
        if (traceExplorer != null)
        {
            traceExplorer.clear();
            traceExplorer.hide();
        }
    }

    /**
     * Fill data
     */
    public void fill(List problems)
    {
        if (problems == null || problems.isEmpty())
        {
            this.problems = null;
            clear();
            return;
        } else
        {
            this.problems = problems;
            updateView();
        }
    }

    private void updateView()
    {
        IDocument document = detailViewer.getDocument();
        StringBuffer buffer = new StringBuffer();
        List states = null;
        for (int i = 0; i < problems.size(); i++)
        {
            TLCError error = (TLCError) problems.get(i);
            appendError(buffer, error);
            if (error.hasTrace())
            {
                Assert.isTrue(states == null, "Two traces are provided. Unexpected. This is a bug");
                states = error.getStates();
            }
        }

        // update the trace information
        TraceExplorer traceExplorer;
        if (states != null)
        {
            traceExplorer = (TraceExplorer) UIHelper.openView(TraceExplorer.ID);
            if (traceExplorer != null)
            {
                traceExplorer.fill(states);
            }
        } else
        {
            traceExplorer = (TraceExplorer) UIHelper.findView(TraceExplorer.ID);
            if (traceExplorer != null) 
            {
                traceExplorer.clear();
                traceExplorer.hide();
            }
        }

        // update the error information in the TLC Error View
        try
        {
            document.replace(0, document.getLength(), buffer.toString());
        } catch (BadLocationException e)
        {
            TLCUIActivator.logError("Error reporting the error " + buffer.toString(), e);
        }
    }

    private static void appendError(StringBuffer buffer, TLCError error)
    {
        buffer.append(error.getMessage()).append("\n");
        if (error.getCause() != null)
        {
            appendError(buffer, error.getCause());
        }
    }

    public void hide()
    {
        UIHelper.runUIAsync(new Runnable() {
            public void run()
            {
                getViewSite().getPage().hideView(TLCErrorView.this);
            }
        });
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
     */
    public void setFocus()
    {
        detailViewer.getControl().setFocus();
    }

}
