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

import javax.inject.Inject;

import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.State;
import org.eclipse.core.runtime.Assert;
import org.eclipse.e4.core.di.annotations.Execute;
import org.eclipse.e4.core.services.events.IEventBroker;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.handlers.RegistryToggleState;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.pcal.PCalTranslator;
import org.osgi.service.event.Event;
import org.osgi.service.event.EventHandler;

public class PCalTranslateAutomaticallyHandler extends PCalTranslator implements EventHandler {

	@Inject
	public void initializeAtStartup(final IWorkbench workbench, final ICommandService commandService) {
		/*
		 * Check the UI state of the IHandler/Command which indicates if the user
		 * enabled automatic PlusCal conversion.
		 */
		final Command command = commandService.getCommand("toolbox.command.module.translate.automatially");
		final State state = command.getState(RegistryToggleState.STATE_ID);
		if (!((Boolean) state.getValue()).booleanValue()) {
			return;
		}
		// This IHander is stateful even across Toolbox restarts. In other words, if the
		// user enables automatic PlusCal translation, it will remain enabled even after
		// a Toolbox restart. This means we have to register this EventHandler at the
		// IEventBroker during Toolbox startup.
		// It is vital that we use the Workbench's IEventBroker instance. If e.g. we
		// would use an IEventBroker from higher up the IEclipseContext hierarchy, the
		// broker would be disposed when a new spec gets opened while the IHandler's state
		// remains enabled.
		workbench.getService(IEventBroker.class).unsubscribe(this);
		Assert.isTrue(workbench.getService(IEventBroker.class).subscribe(TLAEditor.PRE_SAVE_EVENT, this));
	}
	
	@Execute
	public void execute(final ExecutionEvent event, final IWorkbench workbench) throws ExecutionException {
		// Toggle the IHandler's state at the UI level (check mark on/off) and
		// unsubscribe/subscribe the EventHandler.
		final IEventBroker eventBroker = workbench.getService(IEventBroker.class);
		if (HandlerUtil.toggleCommandState(event.getCommand())) {
			eventBroker.unsubscribe(this);
		} else {
			eventBroker.unsubscribe(this);
			Assert.isTrue(eventBroker.subscribe(TLAEditor.PRE_SAVE_EVENT, this));
		}
	}
	
	/* (non-Javadoc)
	 * @see org.osgi.service.event.EventHandler#handleEvent(org.osgi.service.event.Event)
	 */
	@Override
	public void handleEvent(final Event event) {
		try {
			final TLAEditor editor = (TLAEditor) event.getProperty(IEventBroker.DATA);
			translate(editor, editor.getSite().getShell(), false);
		} catch (InvocationTargetException | InterruptedException e) {
			throw new RuntimeException(e);
		}
	}
}
