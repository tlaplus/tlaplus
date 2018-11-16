package org.lamport.tla.toolbox.tool.tlc.ui.modelexplorer;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;
import org.lamport.tla.toolbox.tool.tlc.model.Model;

/**
 * Our snapshots were displayed in a funky order due to the default comparator
 * (which did String comparsion of the label strings.) They are now sorted in
 * descending (reverse chronological) order.
 * 
 * @see org.eclipse.jface.util.Policy#getDefaultComparator()
 */
public class ModelSnapshotSorter extends ViewerComparator {

	@Override
	public int compare(final Viewer viewer, final Object e1, final Object e2) {
		if ((!(e1 instanceof Model)) || (!(e2 instanceof Model))) {
			return super.compare(viewer, e1, e2);
		} else {
			final Model m1 = (Model) e1;
			final Model m2 = (Model) e2;
			final long t1 = m1.getSnapshotTimeStamp();
			final long t2 = m2.getSnapshotTimeStamp();

			if (t1 < t2) {
				return 1;
			} else if (t1 > t2) {
				return -1;
			}

			return 0;
		}
	}
}
