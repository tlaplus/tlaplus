package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.jface.action.IMenuManager;

/**
 * A read-only version of the {@link TLAEditor}.
 * Simply overrides the necessary methods to make
 * it read-only.
 * 
 * I created this class for opening read-only versions
 * of modules that are saved when a TLC model is run.
 * I could have written a new read-only source viewer for
 * this, but extending {@link TLAEditor} is the easiest
 * way to immediately get all of the features that the
 * editor already offers : syntax coloring, folding, etc.
 * 
 * @author Daniel Ricketts
 *
 */
public class TLAEditorReadOnly extends TLAEditor
{

    public static final String ID = "org.lamport.tla.toolbox.editor.basic.TLAEditorReadOnly";

    public boolean isEditable()
    {
        return false;
    }

    public boolean isEditorInputReadOnly()
    {
        return true;
    }

    public boolean isEditorInputModifiable()
    {
        return false;
    }

    /**
     * TODO Remove items from the context menu that don't make sense
     * for a read-only version of the module.
     */
    protected void editorContextMenuAboutToShow(IMenuManager menuManager)
    {
        menuManager.removeAll();
    }

}
