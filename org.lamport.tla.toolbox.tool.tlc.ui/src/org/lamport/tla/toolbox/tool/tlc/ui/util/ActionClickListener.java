package org.lamport.tla.toolbox.tool.tlc.ui.util;

import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;

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
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.texteditor.ITextEditor;
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
 * TODO this also support listening for keyboard events too, now. We should refactor this, renaming sensibly to reflect both that
 * 			and what we really mean by "Action".
 * 
 * @author Daniel Ricketts
 */
public class ActionClickListener implements MouseListener, KeyListener {
	/**
	 * @see #setNonDefaultObservables(int)
	 */
	public static final int OBSERVE_DEFAULT = 0;
	public static final int OBSERVE_ARROW_KEY = 1 << 1;
	public static final int OBSERVE_SINGLE_CLICK = 1 << 2;
	
	
	private final Viewer viewer;
	private final Set<Class<? extends ITextEditor>> blacklist;
	private final IWorkbenchPart m_partToRefocus;
	
	private final AtomicBoolean m_observeArrowKeyEvents;
	private final AtomicBoolean m_observeSingleClickEvents;

	public ActionClickListener(final Viewer viewer) {
		this(viewer, new HashSet<Class<? extends ITextEditor>>());
	}

	public ActionClickListener(final Viewer variableViewer, final Set<Class<? extends ITextEditor>> editorBlacklist) {
		this(variableViewer, editorBlacklist, null);
	}

	/**
	 * @param workbenchPart if this is non-null, then the potential part focus change which may occur due to Location-based
	 * 			viewing will be followed with first a focus on to this, followed by a focus to the
	 * 			<code>variableViewer</code>'s control.
	 */
	public ActionClickListener(final Viewer variableViewer, final Set<Class<? extends ITextEditor>> editorBlacklist,
			final IWorkbenchPart workbenchPart) {
		viewer = variableViewer;
		blacklist = editorBlacklist;
		m_partToRefocus = workbenchPart;
		m_observeArrowKeyEvents = new AtomicBoolean(false);
		m_observeSingleClickEvents = new AtomicBoolean(false);
	}
	
	/**
	 * @param observablesMask either OBSERVE_DEFAULT (turning off any changes in
	 *                        default behavior or a bitwise-OR'd combination of the
	 *                        OBSERVE_* constants
	 */
	public void setNonDefaultObservables(final int observablesMask) {
		m_observeArrowKeyEvents.set((observablesMask & OBSERVE_ARROW_KEY) == OBSERVE_ARROW_KEY);
		m_observeSingleClickEvents.set((observablesMask & OBSERVE_SINGLE_CLICK) == OBSERVE_SINGLE_CLICK);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.swt.events.MouseListener#mouseDoubleClick(org.eclipse.swt.events.MouseEvent)
	 */
	public void mouseDoubleClick(final MouseEvent event) {
		goToAction(viewer.getSelection(), (event.stateMask & SWT.CTRL) != 0);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.swt.events.MouseListener#mouseDown(org.eclipse.swt.events.MouseEvent)
	 */
	public void mouseDown(final MouseEvent event) {}

	/* (non-Javadoc)
	 * @see org.eclipse.swt.events.MouseListener#mouseUp(org.eclipse.swt.events.MouseEvent)
	 */
	public void mouseUp(final MouseEvent event) {
		if (m_observeSingleClickEvents.get()) {
			goToAction(viewer.getSelection(), (event.stateMask & SWT.CTRL) != 0);
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.swt.events.KeyListener#keyPressed(org.eclipse.swt.events.KeyEvent)
	 */
	public void keyPressed(final KeyEvent event) {}

	/* (non-Javadoc)
	 * @see org.eclipse.swt.events.KeyListener#keyReleased(org.eclipse.swt.events.KeyEvent)
	 */
	public void keyReleased(final KeyEvent event) {
		final int code = event.keyCode;
		
		if (code == SWT.CR) {
			goToAction(viewer.getSelection(), (event.stateMask & SWT.CTRL) != 0);
		} else if ((code == SWT.KEYPAD_DIVIDE) && ((event.stateMask & SWT.ALT) != 0) && (viewer instanceof TreeViewer)) {
			((TreeViewer) viewer).collapseAll();
		} else if (m_observeArrowKeyEvents.get() && ((code == SWT.ARROW_UP) || (code == SWT.ARROW_DOWN))
				&& (viewer instanceof TreeViewer)) {
			goToAction(viewer.getSelection(), false);
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
						if (!TLCUIHelper.jumpToSavedLocation(location, model, blacklist)) {
							UIHelper.jumpToLocation(location, jumpToPCal, m_partToRefocus);
							
							if (m_partToRefocus != null) {
								viewer.getControl().getDisplay().asyncExec(() -> {
									viewer.getControl().forceFocus();
								});
							}
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
