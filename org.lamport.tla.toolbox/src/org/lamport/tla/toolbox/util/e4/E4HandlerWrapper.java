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
package org.lamport.tla.toolbox.util.e4;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExecutableExtension;
import org.eclipse.core.runtime.IExecutableExtensionFactory;
import org.eclipse.core.runtime.Status;
import org.eclipse.e4.core.contexts.ContextInjectionFactory;
import org.eclipse.e4.core.contexts.IEclipseContext;
import org.eclipse.e4.core.di.annotations.Execute;
import org.eclipse.ui.PlatformUI;
import org.lamport.tla.toolbox.Activator;

@SuppressWarnings("unused")
public class E4HandlerWrapper implements IExecutableExtensionFactory, IExecutableExtension {

	private String clazz;

	/* (non-Javadoc)
	 * @see org.eclipse.core.runtime.IExecutableExtensionFactory#create()
	 */
	@Override
	public Object create() throws CoreException {
		try {
			return new E4Handler<>(Class.forName(clazz));
		} catch (ClassNotFoundException e) {
			throw new CoreException(new Status(1, Activator.PLUGIN_ID, e.getMessage(), e));
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.runtime.IExecutableExtension#setInitializationData(org.eclipse.core.runtime.IConfigurationElement, java.lang.String, java.lang.Object)
	 */
	@Override
	public void setInitializationData(IConfigurationElement config, String propertyName, Object data)
			throws CoreException {
		final String defaultHandler = config.getAttribute("defaultHandler");
		if (defaultHandler.contains(":")) {
			clazz = defaultHandler.split(":")[1];
		}
	}
	
	/*******************************************************************************
	 * Copyright (c) 2012, 2015 EclipseSource München GmbH and others.
	 * All rights reserved. This program and the accompanying materials
	 * are made available under the terms of the Eclipse Public License v1.0
	 * which accompanies this distribution, and is available at
	 * http://www.eclipse.org/legal/epl-v10.html
	 *
	 * Contributors:
	 * Jonas Helming <jhelming@eclipsesource.com> - initial API and implementation
	 * Lars Vogel <Lars.Vogel@gmail.com> - Bug 421453
	 ******************************************************************************/
	public static class E4Handler<C> extends AbstractHandler {
		private final C component;

		public E4Handler(Class<C> clazz) {
			final IEclipseContext context = getActiveContext();
			component = ContextInjectionFactory.make(clazz, context);
		}

		private static IEclipseContext getActiveContext() {
			final IEclipseContext parentContext = getParentContext();
			return parentContext.getActiveLeaf();
		}

		private static IEclipseContext getParentContext() {
			return PlatformUI.getWorkbench().getService(IEclipseContext.class);
		}

		/* (non-Javadoc)
		 * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
		 */
		@Override
		public Object execute(ExecutionEvent event) throws ExecutionException {
			// MAK: Add ExecutionEvent to context in order for the component to have it
			// invoked. E.g. stateful handlers will need it.
			getActiveContext().set(ExecutionEvent.class, event);
			try {
				return ContextInjectionFactory.invoke(component, Execute.class, getActiveContext());
			} finally {
				getActiveContext().remove(ExecutionEvent.class);
			}
		}
	}
}
