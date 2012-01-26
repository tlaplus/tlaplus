package org.lamport.tla.toolbox.tool.tlc.ui.util;

import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.widgets.Tree;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.st.Location;

/**
 * A listener that will respond to the user double clicking or selecting an
 * action by opening the module containing that action and highlighting the
 * action. Can jump to the location in a saved module editor if such an editor
 * is already open.
 * 
 * Currently, double clicking or selecting something in a viewer with this as a
 * listener will only do something if the selection is an instance of
 * {@link IModuleLocatable}.
 * {@link org.lamport.tla.toolbox.tool.tlc.output.data.TLCState} and
 * {@link org.lamport.tla.toolbox.tool.tlc.output.data.CoverageInformationItem}
 * implement that interface.
 * 
 * @author Daniel Ricketts
 * 
 */
public class ActionClickListener implements ISelectionChangedListener, MouseListener {

	private final Viewer viewer;

	public ActionClickListener(final Viewer viewer) {
		this.viewer = viewer;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.swt.events.MouseListener#mouseDoubleClick(org.eclipse.swt.events.MouseEvent)
	 */
	public void mouseDoubleClick(MouseEvent event) {
		goToAction(viewer.getSelection(), (event.stateMask & SWT.ALT) != 0);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.swt.events.MouseListener#mouseDown(org.eclipse.swt.events.MouseEvent)
	 */
	public void mouseDown(MouseEvent e) {}

	/* (non-Javadoc)
	 * @see org.eclipse.swt.events.MouseListener#mouseUp(org.eclipse.swt.events.MouseEvent)
	 */
	public void mouseUp(MouseEvent e) {}


	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ISelectionChangedListener#selectionChanged(org.eclipse.jface.viewers.SelectionChangedEvent)
	 */
	public void selectionChanged(final SelectionChangedEvent event) {
		goToAction(event.getSelection());
	}
	
	private void goToAction(final ISelection selection) {
		goToAction(selection, false);
	}

	private void goToAction(final ISelection selection, boolean jumpToPCal) {
		if (selection != null && !selection.isEmpty()) {
			if (selection instanceof StructuredSelection) {
				final StructuredSelection structuredSelection = (StructuredSelection) selection;
				// on a double click there should not be multiple selections,
				// so taking the first element of the structured selection
				// should work
				final Object firstElement = structuredSelection.getFirstElement();
				if (firstElement instanceof IModuleLocatable) {
					final IModuleLocatable moduleLocatable = (IModuleLocatable) firstElement;
					final Location location = moduleLocatable.getModuleLocation();
					if (location != null) {
						
						/*
						 * jumpToNested will be true if the location could be
						 * shown in a nested saved module editor. If it is
						 * false, we jump to the regular TLA editor instead.
						 */
						final boolean jumpedToNested = TLCUIHelper
								.jumpToSavedLocation(location, ModelHelper
										.getModelByName(moduleLocatable
												.getModelName()));
						if (!jumpedToNested) {
							UIHelper.jumpToLocation(location);
						}
					}
				}
			}
		}
	}
}
