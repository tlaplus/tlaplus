package org.lamport.tla.toolbox.tool.tlc.ui.util;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextInputListener;
import org.eclipse.jface.text.ITextListener;
import org.eclipse.jface.text.TextEvent;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.ui.forms.AbstractFormPart;

/**
 * Mars parts dirty on input
 * @author Simon Zambrovski
 * @version $Id$
 */
public class DirtyMarkingListener implements ITextInputListener, ITextListener, SelectionListener, IgnoringListener
{
    private final AbstractFormPart part;
    private boolean ignoreInputChange;
    
    public DirtyMarkingListener(AbstractFormPart part, boolean ignoreInputChange)
    {
        this.part = part;
        this.ignoreInputChange = ignoreInputChange;
    }

    /**
     * Switches the listner on/off
     * @param ignoreInputChange if true, the listener is deactivated
     */
    public void setIgnoreInput(boolean ignoreInputChange)
    {
        this.ignoreInputChange = ignoreInputChange;
    }

    
    public void inputDocumentAboutToBeChanged(IDocument oldInput, IDocument newInput)
    {
    }

    public void inputDocumentChanged(IDocument oldInput, IDocument newInput)
    {
        if (!ignoreInputChange) 
        {
            part.markDirty();
        }
    }

    public void textChanged(TextEvent event)
    {
        if (!ignoreInputChange) 
        {
            part.markDirty();
        }
    }

    
    public void widgetDefaultSelected(SelectionEvent e)
    {
    }

    public void widgetSelected(SelectionEvent e)
    {
        if (!ignoreInputChange) 
        {
            part.markDirty();
        }
    }
}