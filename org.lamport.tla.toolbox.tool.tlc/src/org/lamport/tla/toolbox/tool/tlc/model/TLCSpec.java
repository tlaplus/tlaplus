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

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchManager;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;

/**
 * {@link TLCSpec} is the glue between {@link Spec} and {@link Model}. Why do we
 * need glue? The Toolbox is written in a modular style. Thus, it is
 * (theoretically) possible to use the Toolbox with all TLC specifics stripped.
 * When thats done, the {@link Model} class would not be available to
 * {@link Spec} which in turn will make it fail to load by the classloader.
 * <p>
 * The general pattern to lookup a {@link Model} instance when you have a
 * {@link Spec}, is to either do Spec.getAdapter(TLCClass.class).getModels() and
 * select the desired instance from the {@link Map}. Or
 * Spec.getAdapter(TLCClass.class).getModel(Fully Qualified Model Name).
 */
public class TLCSpec extends Spec {

	/**
	 * Only supposed to be called by {@link TLCSpecFactory}
	 */
	TLCSpec(Spec spec) {
		super(spec.getProject());
	}

	/**
     * @return All {@link Model}s associated with the given {@link Spec}
	 */
	public Map<String, Model> getModels() {
		final ILaunchConfiguration[] launchConfigurations = getAllLaunchConfigurations();
    	
		final Map<String, Model> res = new HashMap<String, Model>();

    	final IPath location = getProject().getLocation();
		for (int i = 0; i < launchConfigurations.length; i++) {
			final ILaunchConfiguration aConfiguration = launchConfigurations[i];
			if (location.isPrefixOf(aConfiguration.getFile().getLocation())) {
				final Model model = aConfiguration.getAdapter(Model.class);
				res.put(model.getName(), model);
			}
		}
    	
    	return res;
	}
	
    private static ILaunchConfiguration[] getAllLaunchConfigurations() {
		final ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
		final ILaunchConfigurationType launchConfigurationType = launchManager
				.getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_CONFIGURATION_TYPE);
		try {
			return launchManager.getLaunchConfigurations(launchConfigurationType);
		} catch (CoreException shouldNeverHappen) {
			shouldNeverHappen.printStackTrace();
			return new ILaunchConfiguration[0];
		}
    }

	public Model getModel(final String modelName) {
		return getModels().get(Model.sanitizeName(modelName));
	}

	public void rename(final Spec aNewSpec) {
		// The specs name is changed in Spec. What is left, is to fix up the
		// model names. A model name is prefix with the spec's name.
		// Note that the triggering event is sent prior to the actual spec
		// rename. The result returned by Spec#getName() is still the old one.
		final Collection<Model> models = getModels().values();
		for (Model model : models) {
			model.specRename(aNewSpec);
		}
	}

    /**
     * Constructs the model called Foo___Model_1 from the SpecName Foo
     * if Foo___Model_1 already exists, delivers Foo___Model_2, and so on...
     * 
     * This method tests the existence of the launch configuration AND of the file
     * 
     * @return
     */
	public String getModelNameSuggestion() {
		return getModelNameSuggestion("Model_1");
	}
		
	private String getModelNameSuggestion(String proposition) {
		Model model = getModel(proposition);
		if (model != null || getProject().getFile(proposition + ".tla").exists()) {
			String oldNumber = proposition.substring(proposition.lastIndexOf("_") + 1);
			int number = Integer.parseInt(oldNumber) + 1;
			proposition = proposition.substring(0, proposition.lastIndexOf("_") + 1);
			return getModelNameSuggestion(proposition + number);
		}

		return proposition;
	}
	
	/**
	 * Try to be clever in proposing a name for the clone. If the list
	 * of models (related to that spec) follows the Model_1, ...,
	 * Model_23, the name to suggest will be Model_24. If the sequence
	 * has gaps, the lowest gap is chosen starting at model.
	 */
	public String getModelNameSuggestion(final Model model) {
		final String modelName = model.getName();
		final int idx = modelName.lastIndexOf("_");
		if (idx > 0) {
			final String suffix = modelName.substring(idx + 1, modelName.length());
			try {
				Integer.parseInt(suffix);
			} catch (NumberFormatException ignore) {
				// Fall through and suggest basic ..._Copy
				return modelName + "_Copy";
			}
			return getModelNameSuggestion(model.getName());
		}
		return modelName + "_Copy";
	}
}
