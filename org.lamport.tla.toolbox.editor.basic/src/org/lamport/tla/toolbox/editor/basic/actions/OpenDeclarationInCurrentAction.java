package org.lamport.tla.toolbox.editor.basic.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.hyperlink.IHyperlink;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;

public class OpenDeclarationInCurrentAction extends Action implements IHyperlink {
	private final IRegion location;
	private final String label;
	private final IRegion hyperlinkLocation;
	private final TLAEditor editor;

	public OpenDeclarationInCurrentAction(TLAEditor editor, IRegion targetLocation, String hyperlinkLabel, IRegion hyperlinkLocation) {
		super();
		this.editor = editor;
		this.location = targetLocation;
		this.label = hyperlinkLabel;
		this.hyperlinkLocation = hyperlinkLocation;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.action.Action#run()
	 */
	public void run() {
		EditorUtil.setReturnFromOpenDecl();
		this.editor.selectAndReveal(location.getOffset(), location.getLength());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.text.hyperlink.IHyperlink#getHyperlinkRegion()
	 */
	public IRegion getHyperlinkRegion() {
		return this.hyperlinkLocation;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.text.hyperlink.IHyperlink#getHyperlinkText()
	 */
	public String getHyperlinkText() {
		return this.label;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.text.hyperlink.IHyperlink#getTypeLabel()
	 */
	public String getTypeLabel() {
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.jface.text.hyperlink.IHyperlink#open()
	 */
	public void open() {
		run();
	}
}
