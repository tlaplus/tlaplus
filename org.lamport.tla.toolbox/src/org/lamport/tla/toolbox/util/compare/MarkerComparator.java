package org.lamport.tla.toolbox.util.compare;

import java.util.Comparator;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;

/**
 * Compares IMarkers
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class MarkerComparator implements Comparator<IMarker> {

	/* (non-Javadoc)
	 * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
	 */
	public int compare(IMarker m1, IMarker m2) {
		int m1severity = m1.getAttribute(IMarker.SEVERITY,
				IMarker.SEVERITY_INFO);
		int m2severity = m2.getAttribute(IMarker.SEVERITY,
				IMarker.SEVERITY_INFO);

		if (m1severity == m2severity) {
			// same severity, look on the resource
			IResource r1 = m1.getResource();
			IResource r2 = m2.getResource();

			if (r2.equals(r1)) {
				// same resource, look on the line numbers
				int line1 = m1.getAttribute(TLAMarkerHelper.LOCATION_BEGINLINE,
						-1);
				int line2 = m2.getAttribute(TLAMarkerHelper.LOCATION_BEGINLINE,
						-1);

				return new Integer(line2).compareTo(new Integer(line1));

			} else {
				return r2.getName().compareTo(r1.getName());
			}

		} else {
			return new Integer(m2severity).compareTo(new Integer(m1severity));
		}
	}
}
