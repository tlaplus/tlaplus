package org.lamport.tla.toolbox.editor.basic.actions;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.hyperlink.IHyperlink;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Action-based hyperlink implementation 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class OpenDeclarationAction extends Action implements IHyperlink
{
    private IResource resource;
    private IRegion location;
    private String label;

    /**
     * Constructs the action
     * @param resource resource to link
     * @param location location in the resource
     * @param label label of the hyperlink
     */
    public OpenDeclarationAction(IResource resource, IRegion location, String label)
    {
        super();
        this.resource = resource;
        this.location = location;
        this.label = label;
    }

    /**
     * Action method  
     */
    public void run()
    {
        System.out.println("Opening " + label + "(" + resource.getName() + " at " + location + ")");

        TLAEditor editor = (TLAEditor) UIHelper.openEditor(TLAEditor.ID, new FileEditorInput((IFile) resource));
        editor.selectAndReveal(location.getOffset(), location.getLength());

    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.hyperlink.IHyperlink#getHyperlinkRegion()
     */
    public IRegion getHyperlinkRegion()
    {
        return this.location;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.hyperlink.IHyperlink#getHyperlinkText()
     */
    public String getHyperlinkText()
    {
        return this.label;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.hyperlink.IHyperlink#getTypeLabel()
     */
    public String getTypeLabel()
    {
        return null;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.hyperlink.IHyperlink#open()
     */
    public void open()
    {
        run();
    }

}
