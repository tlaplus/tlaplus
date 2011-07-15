package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.swtbot.swt.finder.waits.DefaultCondition;
import org.eclipse.ui.IEditorPart;
import org.lamport.tla.toolbox.editor.basic.TLAEditorAndPDFViewer;
import org.lamport.tla.toolbox.util.UIHelper;

public class SpecEditorOpenCondition extends DefaultCondition {

	private String prefix = "";
	
	public SpecEditorOpenCondition(final String aPrefix) {
		prefix = aPrefix;
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.swtbot.swt.finder.waits.ICondition#test()
	 */
	public boolean test() throws Exception {
		IEditorPart activeEditor = UIHelper.getActiveEditor();
		if(activeEditor instanceof TLAEditorAndPDFViewer) {
			final String aTitle = activeEditor.getTitle();
			return aTitle.startsWith(prefix);
		} 
		return false;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.swtbot.swt.finder.waits.ICondition#getFailureMessage()
	 */
	public String getFailureMessage() {
		return String.format("Timed out waiting for editor with %s to open", prefix);
	}
}
