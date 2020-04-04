package org.lamport.tla.toolbox.tool.tlc.ui.test;

import org.eclipse.swtbot.swt.finder.waits.DefaultCondition;
import org.eclipse.ui.IEditorPart;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Checks if the workbench shows an editor with the given name
 */
public class ModelEditorOpenCondition extends DefaultCondition {

	private final String prefix;
	
	public ModelEditorOpenCondition(String aPrefix) {
		this.prefix = aPrefix;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.swtbot.swt.finder.waits.ICondition#test()
	 */
	public boolean test() throws Exception {
		final IEditorPart activeEditor = UIHelper.getActiveEditor();
		if(activeEditor instanceof ModelEditor) {
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
