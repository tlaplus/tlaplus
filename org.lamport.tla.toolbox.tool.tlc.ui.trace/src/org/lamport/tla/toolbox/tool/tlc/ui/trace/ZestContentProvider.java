package org.lamport.tla.toolbox.tool.tlc.ui.trace;

import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.zest.core.viewers.IGraphEntityContentProvider;

import tlc2.tool.TLCStateInfo;

public class ZestContentProvider extends ArrayContentProvider implements IGraphEntityContentProvider {

	/* (non-Javadoc)
	 * @see org.eclipse.zest.core.viewers.IGraphEntityContentProvider#getConnectedTo(java.lang.Object)
	 */
	public Object[] getConnectedTo(Object entity) {
		if(entity instanceof TLCStateInfo) {
			final TLCStateInfo stateInfo = (TLCStateInfo) entity;
			return new TLCStateInfo[]{stateInfo.predecessorState};
		}
		return null;
	}
}
