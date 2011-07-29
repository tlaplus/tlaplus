package org.lamport.tla.toolbox.tool.tlc.ui.trace;

import org.eclipse.jface.viewers.IBaseLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.zest.core.viewers.EntityConnectionData;

import tlc2.tool.TLCStateInfo;

public class ZestLabelProvider extends LabelProvider implements IBaseLabelProvider {

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.LabelProvider#getText(java.lang.Object)
	 */
	public String getText(Object element) {
		if (element instanceof TLCStateInfo) {
			return element.toString();
		} else if (element instanceof EntityConnectionData) {
			return "";
		}
		throw new RuntimeException("Wrong type: "
				+ element.getClass().toString());
	}
}
