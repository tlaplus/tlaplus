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
package org.lamport.tla.toolbox.ui.provider;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.navigator.IDescriptionProvider;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Module;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.provider.SpecContentProvider.Group;

/**
 * Label provider for all toolbox internal elements
 */
public class ToolboxLabelProvider extends LabelProvider implements ILabelProvider, IDescriptionProvider {
	
	public String getText(final Object element) {
		if (element == null) {
			return null;
		}
		if (element instanceof Spec) {
			final Spec spec = (Spec) element;
			final IFile root = spec.getRootFile();
			if (root == null) {
				return null;
			}
			if (root.getName().replaceAll(".tla$", "").equals(spec.getName())) {
				// Don't append name of root module if identical to spec name (which is usually
				// the default).
				return spec.getName();
			}
			return spec.getName() + " [ " + root.getName() + " ]";
		} else if (element instanceof Module) {
			return ((Module) element).getModuleName();
		} else if (element instanceof Group) {
			return element.toString();
		}
		return null;
	}

	// This is at least shown in the Toolbox's status line at the bottom.
	public String getDescription(final Object element) {
		if (element instanceof Spec) {
			final Spec spec = (Spec) element;
			final IFile root = spec.getRootFile();
			if (root == null) {
				return super.getText(element);
			}
			return spec.getName() + " [ " + root.getLocation().toFile() + " ]";
		} else if (element instanceof Module) {
			final Module module = (Module) element;
			return module.getModuleName() + " [ " + module.getResource().getLocation().toFile() + " ]";
		}
		return super.getText(element);
	}

	public Image getImage(final Object element) {
		if (element == null) {
			return null;
		}
		if (element instanceof Spec) {
			if (Activator.getSpecManager().isSpecLoaded((Spec) element)) {
				return Activator.getDefault().getImageRegistry().get(Activator.IMG_SPEC_OPEN);
			}
			return Activator.getDefault().getImageRegistry().get(Activator.IMG_SPEC_CLOSED);
		} else if (element instanceof Module) {
			return PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_OBJ_FILE);
		} else if (element instanceof Group) {
			return PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_TOOL_COPY);
		}
		return null;
	}
}