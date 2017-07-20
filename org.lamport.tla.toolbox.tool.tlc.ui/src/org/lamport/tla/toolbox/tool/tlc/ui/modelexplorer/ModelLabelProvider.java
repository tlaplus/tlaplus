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

import java.text.SimpleDateFormat;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.navigator.IDescriptionProvider;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.modelexplorer.ModelContentProvider.Group;

/**
 * Provides labels for the TLC models
 */
public class ModelLabelProvider extends LabelProvider implements IDescriptionProvider {
	private static final SimpleDateFormat sdf = new SimpleDateFormat("MMM dd,yyyy HH:mm:ss");

	private Image modelImage = TLCUIActivator.getImageDescriptor("/icons/full/choice_sc_obj.gif").createImage();
	private Image modelNoError = TLCUIActivator.getImageDescriptor("/icons/full/model_no_error.gif").createImage();
	private Image modelWithError = TLCUIActivator.getImageDescriptor("/icons/full/model_with_error.gif").createImage();
	
	/**
	 * Retrieves model's image
	 */
	public Image getImage(final Object element) {
		if (element instanceof Group) {
			return modelImage;
		} else if (element instanceof Model) {
			final Model model = (Model) element;
			if (model.isSnapshot()) {
				if (model.hasError()) {
					return modelWithError;
				}
				return modelNoError;
			} else {
				return modelImage;
			}
		}
		return super.getImage(element);
	}

	/**
	 * Retrieves model's label
	 */
	public String getText(final Object element) {
		if (element instanceof Model) {
			final Model model = (Model) element;
			if (model.isSnapshot()) {
				return sdf.format(model.getSnapshotTimeStamp());
			}
			final String modelName = model.getName();
			if (model.isStale()) {
				return modelName + " [ crashed ]";
			}
			if (model.isRunning()) {
				return modelName + " [ modelchecking ]";
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
		if (element instanceof Model) {
			final Model model = (Model) element;
			final String comments = model.getComments();
			if (comments.equals("")) {
				return getText(element);
			}
			return comments;
		}
		return null;
	}

	/**
	 * Dispose the image
	 */
	public void dispose() {
		if (modelImage != null) {
			modelImage.dispose();
		}
		modelImage = null;
		if (modelNoError != null) {
			modelNoError.dispose();
		}
		modelNoError = null;
		if (modelWithError != null) {
			modelWithError.dispose();
		}
		modelWithError = null;
		super.dispose();
	}
}
