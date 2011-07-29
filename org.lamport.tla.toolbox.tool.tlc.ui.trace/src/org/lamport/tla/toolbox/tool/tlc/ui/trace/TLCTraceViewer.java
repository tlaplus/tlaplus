package org.lamport.tla.toolbox.tool.tlc.ui.trace;

import java.io.File;
import java.io.IOException;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.Separator;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.zest.core.viewers.AbstractZoomableViewer;
import org.eclipse.zest.core.viewers.GraphViewer;
import org.eclipse.zest.core.viewers.IZoomableWorkbenchPart;
import org.eclipse.zest.core.viewers.ZoomContributionViewItem;
import org.eclipse.zest.layouts.LayoutAlgorithm;
import org.eclipse.zest.layouts.LayoutStyles;
import org.eclipse.zest.layouts.algorithms.TreeLayoutAlgorithm;
import org.lamport.tla.toolbox.util.ToolboxJob;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * @see http://www.vogella.de/articles/EclipseZest/article.html
 */
public class TLCTraceViewer extends ViewPart implements IZoomableWorkbenchPart {

	/**
	 * The ID of the view as specified by the extension.
	 */
	public static final String ID = "org.lamport.tla.toolbox.tool.tlc.ui.trace.TLCTraceViewer";
	
	private GraphViewer viewer;

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
	 */
	public void createPartControl(Composite parent) {
		viewer = new GraphViewer(parent, SWT.BORDER);

		// how nodes are connected to each other
		viewer.setContentProvider(new ZestContentProvider());
		
		// how nodes look like
		viewer.setLabelProvider(new ZestLabelProvider());
		
		// a Tree based layout
		final LayoutAlgorithm layout = new TreeLayoutAlgorithm(LayoutStyles.NO_LAYOUT_NODE_RESIZING);
		viewer.setLayoutAlgorithm(layout, true);

		fillToolBar();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
	 */
	public void setFocus() {
		viewer.getControl().setFocus();
	}
	
	/**
	 * Adds actions to the view's tool bar
	 * - A zoom action
	 * - Open trace action
	 * - layout grapth/tree action
	 */
	private void fillToolBar() {
		final IActionBars bars = getViewSite().getActionBars();
		bars.getMenuManager().add(new AddFileAction());
		bars.getMenuManager().add(new LayoutAction());
		bars.getMenuManager().add(new Separator());
		bars.getMenuManager().add(new ZoomContributionViewItem(this));
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.zest.core.viewers.IZoomableWorkbenchPart#getZoomableViewer()
	 */
	public AbstractZoomableViewer getZoomableViewer() {
		return viewer;
	}

	public class AddFileAction extends Action implements IAction {
		
		public AddFileAction() {
			super("Open Trace");
			this.setDescription("Open trace file");
			this.setToolTipText("Opens TLC Trace File Viewer on the given trace file.");
		}

		/* (non-Javadoc)
		 * @see org.eclipse.jface.action.Action#run()
		 */
		public void run() {
			// prompt user for trace file path
			FileDialog fd = new FileDialog(getSite().getShell(), SWT.OPEN);
			fd.setFileName("/path/of/MC.st");
			fd.setFilterExtensions(new String[]{"*.st"});
			fd.setText("Choose TLC trace file to open (*.st)");
			final String tracePath = fd.open();

			fd = new FileDialog(getSite().getShell(), SWT.OPEN);
			fd.setFileName(tracePath);
			fd.setFilterExtensions(new String[]{"*.tla"});
			fd.setText("Choose corresponding TLC spec (*.tla)");
			final String specPath = fd.open();
			
			if(tracePath != null && !"".equals(tracePath) && specPath != null && !"".equals(specPath)) {
				final File traceFile = new File(tracePath);
				final File specFile = new File(specPath);
				Assert.isTrue(traceFile.exists());
				Assert.isTrue(specFile.exists());

				// connects the UI to the model
				final Job job = new ToolboxJob("Parsing TLC trace file...") {
					/* (non-Javadoc)
					 * @see org.eclipse.core.runtime.jobs.Job#run(org.eclipse.core.runtime.IProgressMonitor)
					 */
					protected IStatus run(final IProgressMonitor monitor) {
						try {
							final TLCTraceFileModelProvider model = new TLCTraceFileModelProvider(specFile, traceFile);
							UIHelper.runUIAsync(new Runnable() {
								/* (non-Javadoc)
								 * @see java.lang.Runnable#run()
								 */
								public void run() {
									viewer.setInput(model.getTrace());
									viewer.applyLayout();
								}
							});
						} catch (IOException e) {
							return Status.CANCEL_STATUS;
						}
						return Status.OK_STATUS;
					}
				};
				job.schedule();
			}
		}
	}
	
	public class LayoutAction extends Action implements IAction {
		
		public LayoutAction() {
			super("Layout Tree");
			this.setDescription("Layouts the tree");
			this.setToolTipText("Layouts the tree.");
		}

		/* (non-Javadoc)
		 * @see org.eclipse.jface.action.Action#run()
		 */
		public void run() {
			viewer.applyLayout();
		}
	}
}