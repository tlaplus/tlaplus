/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.editor.basic.handlers;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.State;
import org.eclipse.e4.core.services.events.IEventBroker;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.handlers.RegistryToggleState;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.pcal.PCalTranslator;
import org.osgi.service.event.Event;
import org.osgi.service.event.EventHandler;

public class PCalTranslateAutomaticallyHandler extends PCalTranslator implements EventHandler {

	public PCalTranslateAutomaticallyHandler() {
		// This IHander is stateful even across Toolbox restarts. In other words, if the
		// user requests automatic PlusCal translation, it will enabled even after a
		// Toolbox restart. This means we have to register this at the IEventBroker
		// during Toolbox startup.
		// It is vital that we use the Workbench's IEventBroker instance. If e.g. we
		// would use an IEventBroker from higher up the IEclipseContext hierarchy, the
		// broker would be disposed when a new spec gets opened but the IHandler's state
		// remains enabled.
		final IEventBroker service = PlatformUI.getWorkbench().getService(IEventBroker.class);
		service.subscribe(TLAEditor.PRE_SAVE_EVENT, this);
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
	 */
	public Object execute(final ExecutionEvent event) throws ExecutionException {
		// Toggle the IHandler's state at the UI level (check mark on/off). The
		// IEventBroker handler remains subscribed to the event bus but will simply
		// ignore the events.
		HandlerUtil.toggleCommandState(event.getCommand());
		return null;
	}
	
	/* (non-Javadoc)
	 * @see org.osgi.service.event.EventHandler#handleEvent(org.osgi.service.event.Event)
	 */
	@Override
	public void handleEvent(final Event event) {
		if (!isAutomaticEnabled()) {
			// If the UI state is false, the user doesn't want automatic PlusCal translation.
			return;
		}
		try {
			final TLAEditor editor = (TLAEditor) event.getProperty(IEventBroker.DATA);
			translate(editor, editor.getSite().getShell(), false);
		} catch (InvocationTargetException | InterruptedException e) {
			throw new RuntimeException(e);
		}
	}
	
	/*
	 * Check the UI state of the IHandler/Command which indicates if the user
	 * enabled automatic PlusCal conversion.
	 */
	private static boolean isAutomaticEnabled() {
		final ICommandService service = PlatformUI.getWorkbench().getService(ICommandService.class);
		final Command command = service.getCommand("toolbox.command.module.translate.automatially");
		final State state = command.getState(RegistryToggleState.STATE_ID);
		return ((Boolean) state.getValue()).booleanValue();
	}
}
