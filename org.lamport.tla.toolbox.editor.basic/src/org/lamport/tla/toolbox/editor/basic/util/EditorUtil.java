package org.lamport.tla.toolbox.editor.basic.util;

import org.eclipse.ui.IEditorPart;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.TLAEditorAndPDFViewer;
import org.lamport.tla.toolbox.util.UIHelper;

public class EditorUtil
{

    /**
     * Returns the {@link TLAEditor} with focus or null if
     * there is none.
     * 
     * @return
     */
    public static TLAEditor getTLAEditorWithFocus()
    {
        IEditorPart activeEditor = UIHelper.getActivePage().getActiveEditor();
        // activeEditor.getAdapter(ITexto)
        if (activeEditor instanceof TLAEditorAndPDFViewer)
        {
            TLAEditor editor = ((TLAEditorAndPDFViewer) activeEditor).getTLAEditor();
            if (editor != null && editor.getViewer().getTextWidget().isFocusControl())
            {
                return editor;
            }
        }

        return null;
    }

}
