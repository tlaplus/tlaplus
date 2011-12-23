// Copyright (c) Dec 22, 2011 Microsoft Corporation.  All rights reserved.

package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import org.eclipse.core.runtime.Assert;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IMemento;
import org.eclipse.ui.INavigationLocation;

/**
 * @author Markus Alexander Kuppe
 */
public class ControlNavigationLocation implements INavigationLocation {

	private Control control;

	public ControlNavigationLocation(Control aControl) {
		Assert.isNotNull(aControl);
		control = aControl;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#dispose()
	 */
	public void dispose() {
		releaseState();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#releaseState()
	 */
	public void releaseState() {
		control = null;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#saveState(org.eclipse.ui.IMemento)
	 */
	public void saveState(IMemento memento) {
		// no-op because we don't support persistent navigation history
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#restoreState(org.eclipse.ui.IMemento)
	 */
	public void restoreState(IMemento memento) {
		// no-op because we don't support persistent navigation history
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#restoreLocation()
	 */
	public void restoreLocation() {
		if(control != null) {
			control.setFocus();
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#mergeInto(org.eclipse.ui.INavigationLocation)
	 */
	public boolean mergeInto(INavigationLocation currentLocation) {
		return false;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#getInput()
	 */
	public Object getInput() {
		return control;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#getText()
	 */
	public String getText() {
		// if null the navigation history just uses the part's name
		return null;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#setInput(java.lang.Object)
	 */
	public void setInput(Object input) {
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#update()
	 */
	public void update() {
	}
}
