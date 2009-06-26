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
    private final IRegion hyperlinkLocation;

    /**
     * Constructs the action
     * @param targetResource resource to link
     * @param targetLocation location in the resource
     * @param hyperlinkLabel label of the hyperlink
     * @param hyperlinkLocation location of the hyperlink
     */
    public OpenDeclarationAction(IResource targetResource, IRegion targetLocation, String hyperlinkLabel, IRegion hyperlinkLocation)
    {
        super();
        this.resource = targetResource;
        this.location = targetLocation;
        this.label = hyperlinkLabel;
        this.hyperlinkLocation = hyperlinkLocation;
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
        return this.hyperlinkLocation;
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
