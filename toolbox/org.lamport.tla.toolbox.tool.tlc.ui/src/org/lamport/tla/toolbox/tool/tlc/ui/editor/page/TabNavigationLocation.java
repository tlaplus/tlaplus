// Copyright (c) Dec 20, 2011 Microsoft Corporation.  All rights reserved.

package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import org.eclipse.ui.IMemento;
import org.eclipse.ui.INavigationLocation;
import org.eclipse.ui.forms.editor.IFormPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;

/**
 * @author Markus Alexander Kuppe
 */
public class TabNavigationLocation implements INavigationLocation {

	private IFormPage formPage;
	private Object input;
	
	public TabNavigationLocation(IFormPage aFormPage) {
		this.formPage = aFormPage;
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
		ModelEditor me = (ModelEditor) formPage.getEditor();
		me.setActivePage(formPage.getIndex());
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#mergeInto(org.eclipse.ui.INavigationLocation)
	 */
	public boolean mergeInto(INavigationLocation currentLocation) {
		// merge this and the given currentLocation if they both are the same type and handle the same page
		if(currentLocation instanceof TabNavigationLocation) {
			TabNavigationLocation fpnlc = (TabNavigationLocation) currentLocation;
			return formPage == fpnlc.formPage;
		}
		return false;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocation#update()
	 */
	public void update() {
		// nothing to update yet
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.NavigationLocation#dispose()
	 */
	public void dispose() {
		releaseState();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.NavigationLocation#releaseState()
	 */
	public void releaseState() {
		this.input = null;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.NavigationLocation#getInput()
	 */
	public Object getInput() {
		return this.input;	
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.NavigationLocation#getText()
	 */
	public String getText() {
		final String title = this.formPage.getTitle();
		return title;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.NavigationLocation#setInput(java.lang.Object)
	 */
	public void setInput(Object input) {
		this.input = input;
	}
}
