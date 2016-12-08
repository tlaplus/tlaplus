// Copyright (c) Dec 08, 2016 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.toolbox;

import java.io.File;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.e4.core.services.events.IEventBroker;
import org.eclipse.e4.ui.workbench.UIEvents;
import org.eclipse.e4.ui.workbench.lifecycle.PostContextCreate;
import org.eclipse.equinox.app.IApplicationContext;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.ui.handler.NewSpecHandler;
import org.lamport.tla.toolbox.ui.handler.OpenSpecHandler;
import org.lamport.tla.toolbox.util.UIHelper;

@SuppressWarnings("restriction")
public class OpenFileManager implements Listener {
	
	@PostContextCreate
	void postContextCreate(final IApplicationContext appContext, final Display display, final IEventBroker broker) {
		// postContextCreate is registered as a LifeCycle listener via
		// ../org.lamport.tla.toolbox.product.standalone/plugin.xml. When it is
		// called, the Eclipse workbench has not been created yet. Thus, we
		// register with the IEventBroker to be notified once the workbench is
		// there. We then spawn a Runnable to let the Toolbox UI fully come up
		// before we call the open/new handler.
		broker.subscribe(UIEvents.UILifeCycle.ACTIVATE, new org.osgi.service.event.EventHandler() {
			/* (non-Javadoc)
			 * @see org.osgi.service.event.EventHandler#handleEvent(org.osgi.service.event.Event)
			 */
			public void handleEvent(org.osgi.service.event.Event event) {
				// We do not want to be called again.
				broker.unsubscribe(this);
				
				UIHelper.runUIAsync(new Runnable() {
					public void run() {
						final Object argObject = appContext.getArguments().get(IApplicationContext.APPLICATION_ARGS);
						if (argObject != null && argObject instanceof String[]) {
							final String[] args = (String[]) argObject;
							if (args.length > 0) {
								openOrCreateSpec(args[0]);
							}
						} else if (argObject != null && argObject instanceof String) {
							openOrCreateSpec((String) argObject);
						}
						
						// After we have handled the file parameter with which
						// the Toolbox got started, we now registered for
						// subsequent file open calls, see handleEvent(Event).
						display.addListener(SWT.OpenDocument, OpenFileManager.this);
					}
				});
			}
		});
	}

	/* (non-Javadoc)
	 * @see org.eclipse.swt.widgets.Listener#handleEvent(org.eclipse.swt.widgets.Event)
	 */
	public void handleEvent(Event event) {
		final String absolutePath = event.text;
		if (absolutePath != null) {
			openOrCreateSpec(absolutePath);
		}
	}
	
	private void openOrCreateSpec(final String file) {
		// Convert relative file to absolute one if necessary.
		File absoluteFile = new File(file);
		if (!absoluteFile.isAbsolute()) {
			final String absolutePath = new File(".").getAbsolutePath();
			absoluteFile = new File(absolutePath + File.separator + file);
		}
		
		if (absoluteFile.exists() && absoluteFile.isFile()) {
			final Map<String, String> parameters = new HashMap<String, String>();

			// Try to find the corresponding spec.
			final WorkspaceSpecManager specManager = Activator.getSpecManager();
			final Spec spec = specManager.getSpecByRootModule(absoluteFile.getAbsolutePath());
			
			if (spec != null) {
				// Open the spec.
				parameters.put(OpenSpecHandler.PARAM_SPEC, spec.getName());
				UIHelper.runCommand(OpenSpecHandler.COMMAND_ID, parameters);
			} else {
				// Prompt the user to add a new spec.
				parameters.put(NewSpecHandler.PARAM_PATH, absoluteFile.getAbsolutePath());
				UIHelper.runCommand(NewSpecHandler.COMMAND_ID, parameters);
			}
		}
	}
}
