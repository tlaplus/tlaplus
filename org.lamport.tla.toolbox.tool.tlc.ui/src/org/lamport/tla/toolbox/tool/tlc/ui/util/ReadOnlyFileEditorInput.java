package org.lamport.tla.toolbox.tool.tlc.ui.util;

import org.eclipse.core.resources.IFile;
import org.eclipse.ui.IPersistableElement;
import org.eclipse.ui.part.FileEditorInput;

/**
 * Read only editor input
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ReadOnlyFileEditorInput extends FileEditorInput
{

    public ReadOnlyFileEditorInput(IFile file)
    {
        super(file);
    }

    public IPersistableElement getPersistable()
    {
        return null;
    }

}
