package org.lamport.tla.toolbox.util.compare;

import java.util.Comparator;

import org.eclipse.core.resources.IResource;

/**
 * Compare resources based on the name, ignoring the case
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ResourceNameComparator implements Comparator<IResource>
{

	/* (non-Javadoc)
	 * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
	 */
	public int compare(IResource o1, IResource o2) {
		return o1.getName().compareToIgnoreCase(o2.getName());
	}
}
