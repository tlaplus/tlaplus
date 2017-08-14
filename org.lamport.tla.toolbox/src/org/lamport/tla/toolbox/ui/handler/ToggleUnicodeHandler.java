package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.ui.handlers.HandlerUtil;
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
	public static final String ID_TOGGLE_UNICODE = "toolbox.command.module.toggleUnicode";
	
	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.
	 * ExecutionEvent)
	 */
	public Object execute(ExecutionEvent event) throws ExecutionException {

		// final IRegion lineInfo = doc.getLineInformationOfOffset(offset);
	    final Command command = event.getCommand();
		switch(command.getId()) {
		case ID_TOGGLE_UNICODE:
			TLAUnicodeReplacer.setUnicode(!HandlerUtil.toggleCommandState(command));
			break;
		default:
			Activator.getDefault().logInfo("Unrecognized command.");
			return null;
		}


		return null;
	}
}
