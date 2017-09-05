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

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.ui.navigator.CommonViewer;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.model.Model.StateChangeListener;
import org.lamport.tla.toolbox.tool.tlc.model.Model.StateChangeListener.ChangeEvent.State;
import org.lamport.tla.toolbox.tool.tlc.model.TLCSpec;
import org.lamport.tla.toolbox.ui.provider.IGroup;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Provides information about TLC models (launch configurations) in the current
 * project
 */
public class ModelContentProvider implements ITreeContentProvider {
	// content extension for the Toolbox explorer contributed by the TLC
	public static final String TLC_NCE = "toolbox.content.ModelContent";
	private static final Object[] EMPTY_ARRAY = new Object[0];
	
	private final Map<Model, Group> reverse = new HashMap<Model, Group>();
	private final MyStateChangeListener modelChangeListener = new MyStateChangeListener() {
		@Override
		public boolean handleChange(final ChangeEvent event) {
			if (event.getState() == State.DELETED) {
				UIHelper.runUISync(new Runnable() {
					@Override
					public void run() {
						final Model snapshot = event.getModel();
						final Model parent = snapshot.getSnapshotFor();
						// The CommonViewer is stupid in that it accesses an element (snapshot) even
						// after it has been removed in order to update the viewer's current selection.
						// Since we have to prevent this access to avoid a null pointer, we explicitly
						// reset the selection.
						getViewer().setSelection(new StructuredSelection(parent));
						// ...still remove the element from the tree.
						getViewer().remove(parent, new Object[] {snapshot});
					}
				});
			}
			return true;
		}
	};
	
	public Object[] getChildren(final Object parentElement) {
		if (parentElement instanceof Spec) {
			final Spec currentSpec = (Spec) parentElement;
			// only get models of the current spec
			if (ToolboxHandle.getCurrentSpec() == parentElement) {
				final Collection<Model> models = currentSpec.getAdapter(TLCSpec.class).getModels(".*_SnapShot_[0-9]*$", false).values();
				return new Group[] {new Group((Spec) parentElement, models.toArray(new Model[models.size()]))};
			}
		} else if (parentElement instanceof Group) {
			return ((Group) parentElement).getModels();
		} else if (parentElement instanceof Model) {
			final Collection<Model> snapshots = ((Model) parentElement).getSnapshots();
			for (final Model model : snapshots) {
				model.add(modelChangeListener);
			}
			return snapshots.toArray(new Model[snapshots.size()]);
		}
		return EMPTY_ARRAY;
	}

	public Object getParent(final Object element) {
		if (element instanceof Model) {
			final Model model = (Model) element;
			if (model.isSnapshot()) {
				return model.getSnapshotFor();
			}
			return model.getSpec();
		}
		return null;
	}

	public boolean hasChildren(final Object element) {
		if (element instanceof Group) {
			return ((Group) element).getModels().length > 0;
		} else if (element instanceof Model) {
			return ((Model) element).hasSnapshots();
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
		this.modelChangeListener.setViewer((CommonViewer) viewer);
	}
	
	private static class MyStateChangeListener extends StateChangeListener {

		private CommonViewer viewer;

		public void setViewer(CommonViewer viewer) {
			this.viewer = viewer;
		}
		
		public CommonViewer getViewer() {
			return viewer;
		}
	}

	public static final class Group implements IGroup {
		
		private final Model[] models;
		private final Spec spec;
		
		public Group(Spec spec, Model[] models) {
			this.spec = spec;
			this.models = models;
		}
		
		public Model[] getModels() {
			return models;
		}
		
		public Spec getSpec() {
			return spec;
		}
		
		public String toString() {
			return "models";
		}
		
		/*
		 * equals/hashcode is custom tailored for the ToolboxExplorer's viewer.
		 * If the Group does not implement e/h as below, the viewer changes its
		 * expanded state upon refreshs. Since we know that a spec only ever
		 * has a single "models" group node, we can base equality on the Spec.
		 * Also, the set of models keeps changing which renders it unusable
		 * to determine equality.
		 */

		/* (non-Javadoc)
		 * @see java.lang.Object#hashCode()
		 */
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((spec == null) ? 0 : spec.hashCode());
			return result;
		}

		/* (non-Javadoc)
		 * @see java.lang.Object#equals(java.lang.Object)
		 */
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			Group other = (Group) obj;
			if (spec == null) {
				if (other.spec != null)
					return false;
			} else if (!spec.equals(other.spec))
				return false;
			return true;
		}
	}
}
