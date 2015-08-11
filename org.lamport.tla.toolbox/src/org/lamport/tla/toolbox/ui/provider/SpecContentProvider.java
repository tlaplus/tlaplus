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

import java.util.Hashtable;
import java.util.Vector;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.job.DeleteOutOfSyncJob;
import org.lamport.tla.toolbox.spec.Module;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * Content provider listing the specifications
 */
public class SpecContentProvider implements ITreeContentProvider {
	private static final Object[] EMPTY_ARRAY = new Object[0];
	
	private final Hashtable<Module, Group> reverseLookup;
	
	public SpecContentProvider() {
		reverseLookup = new Hashtable<Module, Group>();
	}

	/**
	 * Retrieves the children
	 */
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof WorkspaceSpecManager) {
			return ((WorkspaceSpecManager) parentElement).getRecentlyOpened();
		} else if (parentElement instanceof Spec) {
			final Spec spec = (Spec) parentElement;
			if (Activator.getSpecManager().isSpecLoaded(spec)) {
				final Module[] constructModules = constructModules(spec);
				final Group group = new Group(spec, constructModules);
				for (int i = 0; i < constructModules.length; i++) {
					final Module module = constructModules[i];
					reverseLookup.put(module, group);
				}
				return new Group[] {group};
			}
			return EMPTY_ARRAY;
		} else if (parentElement instanceof Group) {
			return ((Group) parentElement).getModules();
		} else {
			return EMPTY_ARRAY;
		}
	}

	public Object getParent(Object element) {
		if (element instanceof Spec) {
			return Activator.getSpecManager(); // ResourcesPlugin.getWorkspace().getRoot();
		} else if (element instanceof Group) {
			return Activator.getSpecManager().isSpecLoaded(((Group) element).getSpec());
		} else if (element instanceof Module) {
			return reverseLookup.get(element);
		}
		return null;
	}

	public boolean hasChildren(Object element) {
		// A Spec only has children (visually indicated by a triangle in the
		// Spec Explorer) if it is open.
		if (element instanceof Spec) {
			return Activator.getSpecManager().isSpecLoaded((Spec) element);
		} else if (element instanceof Group) {
			Group group = (Group) element;
			if (Activator.getSpecManager().isSpecLoaded(group.getSpec())) {
				return group.getModules().length > 0;
			}
		}
		return (element instanceof WorkspaceSpecManager
		/* || element instanceof Spec */);
	}

	public Object[] getElements(Object inputElement) {
		return getChildren(inputElement);
	}

	public void dispose() {
		reverseLookup.clear();
	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		// no-op
	}

	protected Module[] constructModules(Spec spec) {
		final Vector<IResource> outOfSyncResourcesToDelete = new Vector<IResource>();
		final Vector<Module> modules = new Vector<Module>();
		final IResource[] moduleResources = spec.getModuleResources();
		for (int i = 0; i < moduleResources.length; i++) {
			// skip non-modules
			if (!ResourceHelper.isModule(moduleResources[i])) {
				continue;
			}
			// skip non-existing files
			if (!moduleResources[i].isSynchronized(IResource.DEPTH_ZERO)) {
				outOfSyncResourcesToDelete.add(moduleResources[i]);
				continue;
			}
			final Module module = new Module(moduleResources[i].getLocation().toOSString());
			modules.add(module);
		}

		final DeleteOutOfSyncJob job = new DeleteOutOfSyncJob(outOfSyncResourcesToDelete);
		job.setRule(ResourceHelper.getDeleteRule(
				(IResource[]) outOfSyncResourcesToDelete.toArray(new IResource[outOfSyncResourcesToDelete.size()])));
		job.schedule(500);

		return (Module[]) modules.toArray(new Module[modules.size()]);
	}
	
	public static class Group implements IGroup {
		private final Module[] modules;
		private final Spec spec;

		public Group(Spec spec, Module[] modules) {
			this.spec = spec;
			this.modules = modules;
		}
		/**
		 * @return the spec
		 */
		public Spec getSpec() {
			return spec;
		}
		/**
		 * @return the modules
		 */
		public Module[] getModules() {
			return modules;
		}

		/* (non-Javadoc)
		 * @see java.lang.Object#toString()
		 */
		@Override
		public String toString() {
			return "modules";
		}
	}
}
