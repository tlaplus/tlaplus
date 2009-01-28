package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.core.runtime.IPath;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.part.FileEditorInput;

/**
 * Basic editor without any additional features
 *
 * @author zambrovski
 */
public class TLAEditor extends TextEditor
{
    /**
     * Constructor
     */
    public TLAEditor()
    {
        super();
        setDocumentProvider(new FileDocumentProvider());
        /*
        getDocumentProvider().addElementStateListener(
                new IElementStateListener() {
            public void elementContentAboutToBeReplaced(Object element)
            {
                System.out.println("elementContentAboutToBeReplaced" + element);
            }

            public void elementContentReplaced(Object element)
            {
                System.out.println("elementContentReplaced" + element);
            }

            public void elementDeleted(Object element)
            {
                System.out.println("elementDeleted" + element);
            }

            public void elementDirtyStateChanged(Object element, boolean isDirty)
            {
                System.out.println("elementDirtyStateChanged" + element);
            }

            public void elementMoved(Object originalElement, Object movedElement)
            {
                System.out.println("elementMoved" + originalElement);
            }
        });
    */
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.texteditor.AbstractTextEditor#init(org.eclipse.ui.IEditorSite, org.eclipse.ui.IEditorInput)
     */
    public void init(IEditorSite site, IEditorInput input) throws PartInitException
    {
        super.init(site, input);
        FileEditorInput finput = (FileEditorInput) input;
        if (input != null)
        {
            IPath path = finput.getPath();
            setContentDescription(path.toString());
        }
    }

}
