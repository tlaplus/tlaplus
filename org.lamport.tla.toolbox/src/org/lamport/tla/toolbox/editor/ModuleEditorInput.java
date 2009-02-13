package org.lamport.tla.toolbox.editor;

import org.eclipse.core.resources.IFile;
import org.eclipse.ui.part.FileEditorInput;

/**
 * Extension of the file editor input, containing additional module information
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModuleEditorInput extends FileEditorInput
{
    private boolean isRoot = false;

    /**
     * Constructor 
     * @param file
     * @deprecated setup the the root module flag
     */
    public ModuleEditorInput(IFile file)
    {
        super(file);
    }

    /**
     * Constructor
     * @param file the file containing the module
     * @param isRoot flag is the module is a root module
     */
    public ModuleEditorInput(IFile file, boolean isRoot)
    {
        super(file);
        setRoot(isRoot);
    }

    /**
     * @param isRoot the isRoot to set
     */
    public void setRoot(boolean isRoot)
    {
        this.isRoot = isRoot;
    }

    /**
     * @return the isRoot
     */
    public boolean isRoot()
    {
        return isRoot;
    }

}
