package org.lamport.tla.toolbox.tool.tlc.ui.util;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextInputListener;
import org.eclipse.jface.text.ITextListener;
import org.eclipse.jface.text.TextEvent;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.ui.forms.AbstractFormPart;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.IValidateble;

/**
 * Mars parts dirty on input
 * @author Simon Zambrovski
 * @version $Id$
 */
public class DirtyMarkingListener implements ITextInputListener, ITextListener, SelectionListener, ModifyListener, IgnoringListener 
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
        perform();
    }

    public void textChanged(TextEvent event)
    {
        perform();
    }

    
    public void widgetDefaultSelected(SelectionEvent e)
    {
    }

    public void widgetSelected(SelectionEvent e)
    {
        perform();
    }

    /* (non-Javadoc)
     * @see org.eclipse.swt.events.ModifyListener#modifyText(org.eclipse.swt.events.ModifyEvent)
     */
    public void modifyText(ModifyEvent e)
    {
        perform();
    }
    
    private void perform()
    {
        if (!ignoreInputChange) 
        {
            part.markDirty();
            if (part instanceof IValidateble)
            {
                ((IValidateble)part).validate();
            }
        }
    }
}