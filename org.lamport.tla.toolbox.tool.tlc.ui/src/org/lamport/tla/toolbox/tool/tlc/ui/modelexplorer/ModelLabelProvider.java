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

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.navigator.IDescriptionProvider;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.modelexplorer.ModelContentProvider.Group;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

/**
 * Provides labels for the TLC models
 */
public class ModelLabelProvider extends LabelProvider implements IDescriptionProvider {
	private Image image = TLCUIActivator.getImageDescriptor("/icons/full/choice_sc_obj.gif").createImage();
	private final ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();

	/**
	 * Retrieves model's image
	 */
	public Image getImage(final Object element) {
		if (element instanceof ILaunchConfiguration || element instanceof Group) {
			return image;
		}
		return super.getImage(element);
	}

	/**
	 * Retrieves model's label
	 */
	public String getText(final Object element) {
		if (element instanceof ILaunchConfiguration) {
			final ILaunchConfiguration config = (ILaunchConfiguration) element;
			final String modelName = ModelHelper.getModelName(config.getFile());
			try {
				if (ModelHelper.isModelStale(config)) {
					return modelName + " [ crashed ]";
				}
				if (ModelHelper.isModelRunning(config)) {
					final ILaunch[] launches = launchManager.getLaunches();
					boolean found = false;
					for (int i = 0; i < launches.length; i++) {
						if (launches[i].getLaunchConfiguration().contentsEqual(config)) {
							found = true;
							break;
						}
					}
					if (found) {
						return modelName + " [ modelchecking ]";
					} else {
						// the MC crashed
						// mark the error
						ModelHelper.staleModel(config);
						return modelName + " [ crashed ]";
					}
				}
			} catch (final CoreException e) {
				TLCUIActivator.getDefault().logError("Error creating description for a model", e);
			}
			return modelName;
		} else if (element instanceof Group) {
			return element.toString();
		}
		return null;
	}

	/**
	 * Description to be shown in the status bar
	 */
	public String getDescription(final Object element) {
		if (element instanceof ILaunchConfiguration) {
			return getText(element);
		}
		return null;

	}

	/**
	 * Dispose the image
	 */
	public void dispose() {
		if (image != null) {
			image.dispose();
		}
		image = null;
		super.dispose();
	}

}
