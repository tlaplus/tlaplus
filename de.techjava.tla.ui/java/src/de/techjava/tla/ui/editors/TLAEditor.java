package de.techjava.tla.ui.editors;

import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.editors.outline.TLAOutlinePage;

/**
 * 
 * TLA+ main editor class
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLAEditor.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public class TLAEditor 
	extends TextEditor 
{
	public TLAEditor() {
		super();
	}
	
	public void dispose() 
	{
		super.dispose();
	}
	/**
	 * @see org.eclipse.ui.texteditor.AbstractDecoratedTextEditor#initializeEditor()
	 */
    protected void initializeEditor() 
    {
        super.initializeEditor();
		setSourceViewerConfiguration(new TLAConfiguration(UIPlugin.getDefault().getColorManager()));
		// setDocumentProvider(new TLADocumentProvider());

    }
    
	/**
	 * @see org.eclipse.core.runtime.IAdaptable#getAdapter(java.lang.Class)
	 */
	public Object getAdapter(Class adapter)
	{
		if ( IContentOutlinePage.class.equals(adapter) ) {
			return new TLAOutlinePage( this );
		}

		return super.getAdapter(adapter);
	}
}
