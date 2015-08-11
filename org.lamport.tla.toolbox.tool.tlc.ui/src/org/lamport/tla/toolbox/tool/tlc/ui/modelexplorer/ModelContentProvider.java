/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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
 *   Simon Zambrovski - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.ui.modelexplorer;

import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.ui.provider.IGroup;

/**
 * Provides information about TLC models (launch configurations) in the current
 * project
 */
public class ModelContentProvider implements ITreeContentProvider {
	// content extension for the Toolbox explorer contributed by the TLC
	public static final String TLC_NCE = "toolbox.content.ModelContent";
	private static final Object[] EMPTY_ARRAY = new Object[0];
	
	private final Map<ILaunchConfiguration, Group> reverse = new HashMap<ILaunchConfiguration, Group>();
	
	public Object[] getChildren(final Object parentElement) {
		if (parentElement instanceof Spec) {
			final Spec currentSpec = (Spec) parentElement;
			final ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();

			final ILaunchConfigurationType configType = launchManager
					.getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_CONFIGURATION_TYPE);

			final Vector<ILaunchConfiguration> models = new Vector<ILaunchConfiguration>();

			final IProject specProject = currentSpec.getProject();
			try {
				final ILaunchConfiguration[] configs = launchManager.getLaunchConfigurations(configType);
				for (int i = 0; i < configs.length; i++) {
					// skip launches from other specs (projects)
					if (!specProject.equals(configs[i].getFile().getProject()) || !configs[i].exists()) {
						continue;
					}
					models.add(configs[i]);
				}
			} catch (final CoreException e) {
				TLCUIActivator.getDefault().logError("Error fetching the models", e);
			}

			// only get models of the current spec
			if (ToolboxHandle.getCurrentSpec() == parentElement) {
				return new Group[] {new Group(models.toArray(new ILaunchConfiguration[models.size()]))};
			}
		} else if (parentElement instanceof Group) {
			return ((Group) parentElement).getModels();
		}
		return EMPTY_ARRAY;
	}

	public Object getParent(final Object element) {
		if (element instanceof ILaunchConfiguration) {
			if (((ILaunchConfiguration) element).exists()) {
				return ToolboxHandle.getSpecByName(((ILaunchConfiguration) element).getFile().getProject().getName());
			}
		}
		return null;
	}

	public boolean hasChildren(final Object element) {
		if (element instanceof Group) {
			return ((Group) element).getModels().length > 0;
		}
		/*
		 * Models are shown for the current spec only
		 */
		return (element instanceof Spec && ToolboxHandle.getCurrentSpec() == element);
	}

	public Object[] getElements(final Object inputElement) {
		return getChildren(inputElement);
	}

	public void dispose() {
		reverse.clear();
	}

	public void inputChanged(final Viewer viewer, final Object oldInput, final Object newInput) {
		// nothing to do
	}

	static final class Group implements IGroup {
		
		private final ILaunchConfiguration[] models;
		
		public Group(ILaunchConfiguration[] iLaunchConfigurations) {
			this.models = iLaunchConfigurations;
		}
		
		public ILaunchConfiguration[] getModels() {
			return models;
		}
		
		public String toString() {
			return "models";
		}
	}
}
