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
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/

package org.lamport.tla.toolbox.tool.tlc.model;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdapterFactory;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationListener;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchManager;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;

public class TLCModelFactory implements IAdapterFactory, ILaunchConfigurationListener {

	private final Map<IFile, Model> launch2model = new HashMap<IFile, Model>();
	
	public TLCModelFactory() {
        final ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        launchManager.addLaunchConfigurationListener(this);
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.core.runtime.IAdapterFactory#getAdapter(java.lang.Object, java.lang.Class)
	 */
	@SuppressWarnings("unchecked")
	public <T> T getAdapter(Object adaptableObject, Class<T> adapterType) {
		if (IResource.class.equals(adapterType) && adaptableObject instanceof Model) {
			// Convert a Model instance to an IResource (to connect SpecExplorer with ShowInSystemExplorerHandler).
			final Model model = (Model) adaptableObject;
			if (model.getFolder().exists()) {
				// Before a model has been checked or validated, the model folder doesn't exist. If it exists,
				// a user is likely more interested to open the folder.
				return (T) model.getFolder();
			}
			return (T) model.getFile();
		}
		if (!Model.class.equals(adapterType)) {
			return null;
		}
		if (adaptableObject instanceof ILaunchConfiguration) {
			final ILaunchConfiguration launchConfiguration = (ILaunchConfiguration) adaptableObject;
			// The ILC instances change all the time due to working copies being
			// created dynamically upon save. Thus, map the various ILC's to one
			// model by using the canonical IFile that all ILC instances are
			// technically represented by.
			final IFile key = launchConfiguration.getFile();
			Assert.isNotNull(key);
			if (!launch2model.containsKey(key)) {
				launch2model.put(key, new Model(launchConfiguration));
			}
			return (T) launch2model.get(key);
		}
		return null;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.runtime.IAdapterFactory#getAdapterList()
	 */
	public Class<?>[] getAdapterList() {
		return new Class[] {ILaunchConfiguration.class, IResource.class};
	}

	/* (non-Javadoc)
	 * @see org.eclipse.debug.core.ILaunchConfigurationListener#launchConfigurationAdded(org.eclipse.debug.core.ILaunchConfiguration)
	 */
	public void launchConfigurationAdded(final ILaunchConfiguration configuration) {
	}

	/* (non-Javadoc)
	 * @see org.eclipse.debug.core.ILaunchConfigurationListener#launchConfigurationChanged(org.eclipse.debug.core.ILaunchConfiguration)
	 */
	public void launchConfigurationChanged(final ILaunchConfiguration configuration) {
	}

	/* (non-Javadoc)
	 * @see org.eclipse.debug.core.ILaunchConfigurationListener#launchConfigurationRemoved(org.eclipse.debug.core.ILaunchConfiguration)
	 */
	public void launchConfigurationRemoved(final ILaunchConfiguration configuration) {
		// If the launch2model mapping has an entry for the removed launch
		// config, also dispose the corresponding Model instance. For example
		// Model#rename(String) internally creates a new ILaunchConfiguration
		// making the old obsolete.
		final IFile key = configuration.getFile();
		Assert.isNotNull(key);
		launch2model.remove(key);
	}

	/**
	 * @see Model#getByName(String)
	 */
	public static Model getByName(final String fullQualifiedModelName) {
		Assert.isNotNull(fullQualifiedModelName);
		Assert.isLegal(fullQualifiedModelName.contains(Model.SPEC_MODEL_DELIM), "Not a full-qualified model name.");
		
        final ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        final ILaunchConfigurationType launchConfigurationType = launchManager
                .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_CONFIGURATION_TYPE);

		try {
			final ILaunchConfiguration[] launchConfigurations = launchManager.getLaunchConfigurations(launchConfigurationType);
			for (int i = 0; i < launchConfigurations.length; i++) {
				// Can do equals here because of full qualified name.
				final ILaunchConfiguration launchConfiguration = launchConfigurations[i];
				if (fullQualifiedModelName.equals(launchConfiguration.getName())) {
					return launchConfiguration.getAdapter(Model.class);
				}
			}
		} catch (CoreException shouldNeverHappen) {
			shouldNeverHappen.printStackTrace();
		}
		
		return null;
	}
	
	public static Model getBy(final IFile aFile) {
		Assert.isNotNull(aFile);
		
        final ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        final ILaunchConfigurationType launchConfigurationType = launchManager
                .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_CONFIGURATION_TYPE);

		try {
			final ILaunchConfiguration[] launchConfigurations = launchManager.getLaunchConfigurations(launchConfigurationType);
			for (int i = 0; i < launchConfigurations.length; i++) {
				final ILaunchConfiguration launchConfiguration = launchConfigurations[i];
				if (aFile.equals(launchConfiguration.getFile())) {
					return launchConfiguration.getAdapter(Model.class);
				}
			}
		} catch (CoreException shouldNeverHappen) {
			shouldNeverHappen.printStackTrace();
		}
		
		return null;
	}
}
