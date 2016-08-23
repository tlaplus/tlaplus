package org.lamport.tla.toolbox.tool.tlc.ui.util;

import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.BusyIndicator;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.widgets.Display;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.model.TLCSpec;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCState;
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
public class ActionClickListener implements MouseListener, KeyListener {
	
	private final Viewer viewer;

	public ActionClickListener(final Viewer viewer) {
		this.viewer = viewer;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.swt.events.MouseListener#mouseDoubleClick(org.eclipse.swt.events.MouseEvent)
	 */
	public void mouseDoubleClick(MouseEvent event) {
		goToAction(viewer.getSelection(), (event.stateMask & SWT.CTRL) != 0);
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
	 * @see org.eclipse.swt.events.KeyListener#keyPressed(org.eclipse.swt.events.KeyEvent)
	 */
	public void keyPressed(KeyEvent e) {}

	/* (non-Javadoc)
	 * @see org.eclipse.swt.events.KeyListener#keyReleased(org.eclipse.swt.events.KeyEvent)
	 */
	public void keyReleased(final KeyEvent event) {
		if (event.keyCode == SWT.CR) {
			goToAction(viewer.getSelection(), (event.stateMask & SWT.CTRL) != 0);
		} else if (event.keyCode == SWT.KEYPAD_DIVIDE && (event.stateMask & SWT.ALT) != 0
				&& this.viewer instanceof TreeViewer) {
			((TreeViewer) this.viewer).collapseAll();
		}
	}
	
	private void goToAction(final ISelection selection, boolean jumpToPCal) {
		if (selection != null && !selection.isEmpty()) {
			if (selection instanceof StructuredSelection) {
				final StructuredSelection structuredSelection = (StructuredSelection) selection;
				// on a double click there should not be multiple selections,
				// so taking the first element of the structured selection
				// should work
				final Object firstElement = structuredSelection.getFirstElement();
				if (firstElement instanceof LoaderTLCState) {
					final LoaderTLCState loader = (LoaderTLCState) firstElement;
					// Loading more states can potentially block for a couple
					// seconds. Thus, give feedback to user.
					BusyIndicator.showWhile(Display.getCurrent(), new Runnable() {
						public void run() {
							loader.loadMore();
						}
					});
				} else if (firstElement instanceof IModuleLocatable) {
					final IModuleLocatable moduleLocatable = (IModuleLocatable) firstElement;
					Location location = moduleLocatable.getModuleLocation();
					if (location != null) {
						/*
						 * jumpToNested will be true if the location could be
						 * shown in a nested saved module editor. If it is
						 * false, we jump to the regular TLA editor instead.
						 */
						Model model = ToolboxHandle.getCurrentSpec().getAdapter(TLCSpec.class).getModel(moduleLocatable
								.getModelName());
						final boolean jumpedToNested = TLCUIHelper
								.jumpToSavedLocation(location, model);
						if (!jumpedToNested) {
							UIHelper.jumpToLocation(location, jumpToPCal);
						}
					}
				} else if (!Platform.getWS().equals(Platform.WS_WIN32) && viewer instanceof TreeViewer) {
					// Windows has built-in expand/collapse on double click
					TreeViewer treeViewer = (TreeViewer) viewer;
					if (treeViewer.getExpandedState(firstElement)) {
						treeViewer.collapseToLevel(firstElement, 1);
					} else {
						treeViewer.expandToLevel(firstElement, 1);
					}
				}
			}
		}
	}
    
    public static class LoaderTLCState extends TLCState {

		private final TLCError error;
		private final int numberOfStatesToShow;
		private final TreeViewer viewer;

		public LoaderTLCState(TreeViewer viewer, int numberOfStatesToShow, TLCError error) {
			super(-1, "Load more...");
			this.viewer = viewer;
			this.numberOfStatesToShow = numberOfStatesToShow;
			this.error = error;
			setLabel(String.format("Load %s additional states...", numberOfStatesToShow));
		}

		public void loadMore() {
			error.reduceTraceRestrictionBy(numberOfStatesToShow);
			viewer.getTree().setItemCount(error.getTraceSize() + (error.isTraceRestricted() ? 1 : 0));
			// Reset the viewer's selection to the empty selection. With empty
			// selection, the subsequent setInput call does *not* invalidate the
			// viewer content provider's lazy policy.
			// Since we know that this loadMore() method is called when the user
			// clicks the first tree item (which is the LoaderTLCState), there
			// is no point in preserving the selection anyway.
			viewer.setSelection(new ISelection() {
				public boolean isEmpty() {
					return true;
				}
			});
			viewer.setInput(error);
		}
    }
}
