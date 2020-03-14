package org.lamport.tla.toolbox.editor.basic.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.hyperlink.IHyperlink;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.TLAEditorAndPDFViewer;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Action-based hyperlink implementation 
 * 
 * An OpenDeclarationAction object is created in  
 * TLAHyperlinkDetector.detectHyperlinks.  Its run method is called
 * to jump to the location of a definition or declaration, which is 
 * in the location field.  It is used in the OpenDeclaration (F3)
 * command.  See the commands in TLAEditor for the OpenDeclarationHandler 
 * nested class.
 * 
 * @author Simon Zambrovski
 */
public class OpenDeclarationAction extends Action implements IHyperlink
{
    private final IEditorInput editorInput;
    private final IRegion location;
    private final String label;
    private final IRegion hyperlinkLocation;
	private final String editorId;

    public OpenDeclarationAction(String editorId, IEditorInput editorInput, IRegion targetLocation, String hyperlinkLabel,
            IRegion hyperlinkLocation)
    {
        super();
		this.editorId = editorId;
        this.editorInput = editorInput;
        this.location = targetLocation;
        this.label = hyperlinkLabel;
        this.hyperlinkLocation = hyperlinkLocation;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.action.Action#run()
     */
    public void run()
    {
        EditorUtil.setReturnFromOpenDecl();
        final IEditorPart editor = UIHelper.openEditor(editorId, editorInput);
        if (editor instanceof TLAEditorAndPDFViewer) {
        	((TLAEditorAndPDFViewer) editor).getTLAEditor().selectAndReveal(location.getOffset(), location.getLength());
        } else if (editor instanceof TLAEditor) {
        	((TLAEditor) editor).selectAndReveal(location.getOffset(), location.getLength());
        } else {
        	TLAEditor adapter = editor.getAdapter(TLAEditor.class);
        	if (adapter != null) {
        		adapter.selectAndReveal(location.getOffset(), location.getLength());
        	}
        }
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
