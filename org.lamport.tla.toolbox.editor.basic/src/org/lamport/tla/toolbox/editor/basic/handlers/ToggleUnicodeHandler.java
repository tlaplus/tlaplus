package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.util.TLAUnicodeReplacer;

/**
 * This is the handler method for the following commands:
 * 
 * Toggle Unicode
 * 
 * @author pron
 * 
 */
public class ToggleUnicodeHandler extends AbstractHandler implements IHandler {
	/*
	 * Command ids.
	 */
	public static final String ID_TOGGLE_UNICODE = "org.lamport.tla.toolbox.editor.basic.toggleUnicode";

	
	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.
	 * ExecutionEvent)
	 */
	public Object execute(ExecutionEvent event) throws ExecutionException {
	
		// final IRegion lineInfo = doc.getLineInformationOfOffset(offset);
		switch(event.getCommand().getId()) {
		case ID_TOGGLE_UNICODE:
			TLAUnicodeReplacer.toggleUnicode();
			break;
		default:
			Activator.getDefault().logInfo("Unrecognized command.");
			return null;
		}


		return null;
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#isEnabled()
	 */
	@Override
	public boolean isEnabled() {
		return super.isEnabled();
	}
}
