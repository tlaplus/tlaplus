// Copyright (c) Dec 22, 2011 Microsoft Corporation.  All rights reserved.

package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.ui.IMemento;
import org.eclipse.ui.INavigationLocation;

/**
 * @author Markus Alexander Kuppe
 */
public class NavigationLocationComposite implements INavigationLocation {

	private final List<INavigationLocation> locations = new ArrayList<INavigationLocation>();

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#dispose()
	 */
	public void dispose() {
		for (INavigationLocation location : locations) {
			location.dispose();
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#releaseState()
	 */
	public void releaseState() {
		for (INavigationLocation location : locations) {
			location.releaseState();
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#saveState(org.eclipse.ui.IMemento)
	 */
	public void saveState(IMemento memento) {
		// unsupported right now
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#restoreState(org.eclipse.ui.IMemento)
	 */
	public void restoreState(IMemento memento) {
		// unsupported right now
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#restoreLocation()
	 */
	public void restoreLocation() {
		for (INavigationLocation location : locations) {
			location.restoreLocation();
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#mergeInto(org.eclipse.ui.INavigationLocation)
	 */
	public boolean mergeInto(INavigationLocation currentLocation) {
		// not supported right now
		return false;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#getInput()
	 */
	public Object getInput() {
		return null;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#getText()
	 */
	public String getText() {
		// super class takes care of setting proper string
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

	public void add(INavigationLocation aNavigationLocation) {
		locations.add(aNavigationLocation);
	}
}
