/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.TreeSet;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.DefaultTextHover;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextHover;
import org.eclipse.jface.text.ITextInputListener;
import org.eclipse.jface.text.ITextPresentationListener;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.JFaceTextUtil;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.IVerticalRuler;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ComboViewer;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.KeyAdapter;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.MouseAdapter;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Cursor;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Widget;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.SourceViewerDecorationSupport;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.TLAEditorActivator;
import org.lamport.tla.toolbox.editor.basic.TLAEditorReadOnly;
import org.lamport.tla.toolbox.editor.basic.TLASourceViewerConfiguration;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.output.data.CoverageInformationItem;
import org.lamport.tla.toolbox.tool.tlc.output.data.ModuleCoverageInformation;
import org.lamport.tla.toolbox.tool.tlc.output.data.Representation;
import org.lamport.tla.toolbox.tool.tlc.output.data.Representation.Grouping;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.util.UIHelper;

public class TLACoverageEditor extends TLAEditorReadOnly {

	static {
		JFaceResources.getColorRegistry().put("LIGHT_GRAY", new RGB(245,245,245));
		JFaceResources.getColorRegistry().put("DARK_GRAY", new RGB(200,200,200));
	}
	
	private static final Color lightGray = JFaceResources.getColorRegistry().get("LIGHT_GRAY");
	private static final Color darkGray = JFaceResources.getColorRegistry().get("DARK_GRAY");

	// Icon displayed left of the editor tab's name.
	protected final Image coverageEditorImage = TLAEditorActivator
			.imageDescriptorFromPlugin(TLCUIActivator.PLUGIN_ID, "/icons/full/report2_obj.gif").createImage();

	private static class ResizeListener implements Listener {
		
		private final Point size = new Point(1024,768);

		@Override
		public void handleEvent(final Event event) {
			final Widget widget = event.widget;
			if (widget instanceof Composite) {
				final Composite c = (Composite) widget;
				size.x = c.getSize().x;
				size.y = c.getSize().y;
			}
		}
		
		public int getWidth() {
			return size.x;
		}
	}
	
	/* TLACoverageEditor */

	private final ResizeListener resizeListener = new ResizeListener();
	
	private ModuleCoverageInformation coverage;

	private Composite heatMapComposite;

	private TLACoveragePainter painter;

	public TLACoverageEditor(final ModuleCoverageInformation coverage) {
		this.coverage = coverage;
	}

	@Override
	public void dispose() {
		painter.queue.offer(TERMINATE);
		super.dispose();
	}

	@Override
	protected ISourceViewer createSourceViewer(final Composite parent, IVerticalRuler ruler, int styles) {
		// Create composite inside of parent (of which we don't control the layout) to
		// place heatMap with a fixed height below the editor.
		
		final Composite composite = new Composite(parent, SWT.BORDER);
		final GridLayout layout = new GridLayout(1, false);
		layout.marginHeight = 0;
		layout.marginWidth = 0;
		layout.horizontalSpacing = 0;
		layout.verticalSpacing = 0;
		composite.setLayout(layout);
		composite.addListener(SWT.Resize, resizeListener);

		// Inside editor use again a FillLayout to let super.create... use all available
		// space.
		final Composite editorComposite = new Composite(composite, SWT.NONE);
		editorComposite.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		final FillLayout fillLayout = new FillLayout(SWT.VERTICAL);
		fillLayout.marginHeight = 0;
		fillLayout.marginWidth = 0;
		fillLayout.spacing = 0;
		editorComposite.setLayout(fillLayout);

		heatMapComposite = new Composite(composite, SWT.BORDER);
		final GridData layoutData = new GridData(SWT.FILL, SWT.TOP, true, false);
		heatMapComposite.setLayoutData(layoutData);

		// Inside of heatMap, use a horizontally FillLayout to place individuals heat
		// map item next to each other.
		heatMapComposite.setLayout(new FillLayout(SWT.HORIZONTAL));
		
		final ISourceViewer createSourceViewer = super.createSourceViewer(editorComposite, ruler, styles);
		
		// Make TLACoverageEditor distinguishable from regular TLAEditor.
		final StyledText textWidget = createSourceViewer.getTextWidget();
		textWidget.setCursor(new Cursor(textWidget.getDisplay(), SWT.CURSOR_HAND));
		// Flash the editor on keystrokes as a form of a visual bell.
		textWidget.addKeyListener(new KeyAdapter() {
			@Override
			public void keyPressed(KeyEvent e) {
				textWidget.setBackground(darkGray);
			}
			@Override
			public void keyReleased(KeyEvent e) {
				textWidget.setBackground(lightGray);
			}
		});
		
		return createSourceViewer;
	}
	
	@Override
	protected void initEditorNameAndDescription(final IEditorInput input) {
		if (input instanceof FileEditorInput) {
			final FileEditorInput fei = (FileEditorInput) input;
			// Replace useless filename extension in tab title with read-only indicator.
            this.setPartName(fei.getName().replaceFirst(".tla$", " (ro)"));
            // Use dedicated image to distinguish from regular TLA editor.
            this.setTitleImage(coverageEditorImage);
		} else {
			TLCActivator.logDebug("Unexpected input for TLACoverageEditor of type: " + input.getClass().getName());
		}
	}

	@Override
    protected TLASourceViewerConfiguration getTLASourceViewerConfiguration(IPreferenceStore preferenceStore) {
    	return new TLACoverageSourceViewerConfiguration(preferenceStore, this); 
    }

	@Override
	protected SourceViewerDecorationSupport getSourceViewerDecorationSupport(ISourceViewer viewer) {
		//TODO Initialize painter after editor input has been set.
		painter = new TLACoveragePainter(this);
		((TextViewer) viewer).addTextPresentationListener(painter);
		
		return super.getSourceViewerDecorationSupport(viewer);
	}

	public void resetInput(final ModuleCoverageInformation ci) throws PartInitException {
		if (this.coverage == ci) {
			// The CoverageInformation from which the FileCoverageInformation has been
			// projected, is identical to the one already open. No need to update the ui.
			// This case occurs when the TLCModelLaunchDataProvider parses the MC.out of a
			// finished model with more than one block of coverage statistics. For each it
			// notifies ResultPage but - due to TLCModelLaunchDataProvider sending strings
			// instead of the actual values and threading - we read a newer/more up-to-date
			// instance of CoverageInformation before a notification reaches us.
			return;
		}
		this.coverage = ci;
		// Trigger the editor's coverage painter.
		painter.queue.offer(ALL);
	}

	/* TLASourceViewerConfiguration */

	private class TLACoverageSourceViewerConfiguration extends TLASourceViewerConfiguration {

		public TLACoverageSourceViewerConfiguration(IPreferenceStore preferenceStore,
				TLAEditor tlaCoverageEditor) {
			super(preferenceStore, tlaCoverageEditor);
		}
		
		@Override
		public ITextHover getTextHover(final ISourceViewer sourceViewer, String contentType) {
			return new DefaultTextHover(sourceViewer) {
				@Override
				public String getHoverInfo(ITextViewer textViewer, IRegion hoverRegion) {
					return coverage.getHoverInfo(hoverRegion.getOffset());
				}
			};
		}
    }
	
	private static final DecimalFormat df = new DecimalFormat("0.0E0");
	
	private static class Pair {
		public final int offset;
		public final Representation rep;

		public Pair(int offset) {
			this(offset, Representation.INV);
		}

		public Pair(int offset, Representation rep) {
			this.offset = offset;
			this.rep = rep;
		}
	}

	private static final Pair ALL = new Pair(-1);
	
	private static final Pair TERMINATE = new Pair(-42);
	
	public class TLACoveragePainter implements ITextPresentationListener {
		
		private ComboViewer viewer;
		
		private final TLACoverageEditor editor;
		
		private final BlockingQueue<Pair> queue = new ArrayBlockingQueue<>(10);
		
		// Each module editor has a painter (system) job which serializes the
		// paint/annotation requests. Requests are generated either by opening the
		// editor, via editor selection changes or legend changes. Requests have
		// to be serialized because ModuleCoverageInformation and its nested data
		// structures are not thread-safe. Additional we try to minimize the requests
		// by skipping redundant requests triggered by rapid mouse clicks.
		private final Job painter = new Job("Coverage Painter") {
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				while (true) {
					final Pair p = getPair();
					if (TERMINATE.offset == p.offset || monitor.isCanceled()) {
						return Status.OK_STATUS;
					} else {
						monitor.beginTask(String.format("Painting coverage for %s", p.offset), 1);
					}
					
					// Do not clear old style ranges before creating new ones as clear removes TLA+ syntax highlighting.
					//textPresentation.clear(); 
					
					final Grouping grouping = ALL.offset == p.offset ? Grouping.COMBINED : Grouping.INDIVIDUAL;
					
					// Create new style ranges (and the legend)
					TreeSet<CoverageInformationItem> legend = new TreeSet<>();
					if (grouping == Grouping.COMBINED) {
						coverage.getRoot().style(textPresentation, p.rep);
						legend = coverage.getLegend(p.rep);
					} else {
						final CoverageInformationItem node = coverage.getNode(p.offset);
						if (node != null) {
							// Style all unrelated parts gray.
							coverage.getRoot().style(textPresentation, JFaceResources.getColorRegistry().get(ModuleCoverageInformation.GRAY), p.rep);
							
							node.style(textPresentation, p.rep);
							legend = node.getLegend(p.rep);
						}
					}
					
					if (monitor.isCanceled()) {
						return Status.OK_STATUS;
					}
					
					final Collection<CoverageInformationItem> fLegend = collapseLegend(legend);
					UIHelper.runUISync(new Runnable() {
						@Override
						public void run() {
							final TextViewer viewer = editor.getViewer();
							// viewer might have been disposed by the time the outer thread styled the presentation.
							if (viewer == null || viewer.getTextWidget() == null
									|| viewer.getTextWidget().isDisposed()) {
								return;
							}
							viewer.getTextWidget().removeListener(SWT.MouseDown, listener);

							viewer.changeTextPresentation(textPresentation, true);
							updateLegend(fLegend, grouping);
							
							viewer.getTextWidget().addListener(SWT.MouseDown, listener);
						}
					});
					
					monitor.done();
				}
			}
			
			private Collection<CoverageInformationItem> collapseLegend(final TreeSet<CoverageInformationItem> legend) {
				final double numLabel = resizeListener.getWidth() / 47d; // 47 pixel per label seems to fit most text and still looks pleasant.
				if (legend.size() <= (int) Math.ceil(numLabel)) {
					// can fit all elements, nothing to do.
					return legend;
				}
				
				// TODO Select a subset of legend of size numLabels s.t. the distance between
				// any two elements in subset is maximized. The code below approximates the
				// problem by simply constructing the subset where the distance is the position
				// in the set not the actual value. In other words, the set of distances of all
				// adjacent elements in the legend will be non-uniform.
				
				// Cannot fit more than N labels into the legend. Thus, only take N elements
				// out of legend (even distribution).
				final int nth = (int) Math.ceil(legend.size() / numLabel);

				// Add lowest/first CCI.
				final List<CoverageInformationItem> result = new ArrayList<>((int)Math.ceil(numLabel));
				result.add(legend.first());

				// Pick nth - 2 CCIs in-between.
				int i = 1;
				final Iterator<CoverageInformationItem> iterator = legend.iterator();
				while (iterator.hasNext()) {
					final CoverageInformationItem cii = iterator.next();
					if (i++ % nth == 0) {
						result.add(cii);
					}
				}
				
				// Add highest/last CCI from legend.
				result.add(legend.last());
				return result;
			}

			private Pair getPair() {
				try {
					return queue.take();
				} catch (InterruptedException notExpectedException) {
					notExpectedException.printStackTrace();
					return TERMINATE;
				}
			}

			private void updateLegend(Collection<CoverageInformationItem> legend, final Representation.Grouping grouping) {
				final Composite parent = heatMapComposite.getParent();
				if (legend.isEmpty()) {
					heatMapComposite.setVisible(false);
				} else {
					final Representation currentRepresentation = getActiveRepresentation();
					heatMapComposite.dispose();
					
					heatMapComposite = new Composite(parent, SWT.BORDER);
					final GridData layoutData = new GridData(SWT.FILL, SWT.TOP, true, false);
					heatMapComposite.setLayoutData(layoutData);
					
					// Inside of heatMap, use a horizontally FillLayout to place individuals heat
					// map item next to each other.
					heatMapComposite.setLayout(new FillLayout(SWT.HORIZONTAL));
					
					// Create the actual SWT labels for the elements in legend. 
					// TODO Rendering the text vertically would save horizontal screen estate but is
					// unfortunately not easily possible with SWT.
					for (CoverageInformationItem cii : legend) {
						final Label label = new Label(heatMapComposite, SWT.BORDER);
						label.setAlignment(SWT.CENTER);
						
						// A label has a background color and a text indicating the actual value
						// (cost/invocations/...).
						label.setBackground(currentRepresentation.getColor(cii, grouping));

						final long value = currentRepresentation.getValue(cii, grouping);
						// Format numbers > 1000 in scientific notation.
						if (value > 1000) {
							label.setText(df.format(value));
						} else {
							label.setText(String.format("%,d", value));
						}
						
						// Indicate the location to where the mouse click takes the user.
						label.setToolTipText(String.format(currentRepresentation.getToolTipText(), value, cii.getLocation()));
						
						// The mouse listener takes the user to the related
						// region in the module.
						label.addMouseListener(new MouseAdapter() {
							@Override
							public void mouseDown(final MouseEvent e) {
								final IRegion region = cii.getRegion();
								editor.selectAndReveal(region.getOffset(), cii.getRegion().getLength());
							}
						});
					}

					// Show a drop-down list (combo) to let the user select a different representation. 
					viewer = new ComboViewer(heatMapComposite, SWT.DROP_DOWN | SWT.READ_ONLY | SWT.BORDER | SWT.WRAP);
				    viewer.setContentProvider(ArrayContentProvider.getInstance());
				    viewer.setLabelProvider(new LabelProvider() {
				        @Override
				        public String getText(Object element) {
				            if (element instanceof Representation) {
				            	Representation current = (Representation) element;
				            	return current.toString();
				            }
				            return super.getText(element);
				        }
				    });
				    
					// Do not allow users to set the legend to states or distinct states if the
					// module does not have values for these two representations. Otherwise, update
					// legend will hide the legend (because legend is empty) without means to switch
					// back (the buttons are hidden).
					viewer.setInput(coverage.hasStates() ? Representation.values() : Representation.valuesNoStates());
				    viewer.setSelection(new StructuredSelection(currentRepresentation));
				    viewer.addSelectionChangedListener(event -> {
					    final IStructuredSelection selection = (IStructuredSelection) event.getSelection();
					    final Representation rep = (Representation)selection.getFirstElement();
						final int offset = JFaceTextUtil.getOffsetForCursorLocation(editor.getViewer());
						queue.offer(new Pair(offset, rep));
					});
				}
				parent.layout();
			}
		};

		private Representation getActiveRepresentation() {
			if (viewer != null) {
				final IStructuredSelection structuredSelection = viewer.getStructuredSelection();
				return (Representation) structuredSelection.getFirstElement();
			}
			return Representation.INV;
		}
		
		private final Listener listener = new Listener() {
			@Override
			public void handleEvent(Event event) {
				final Representation activeRepresentation = getActiveRepresentation();
				final int offset = JFaceTextUtil.getOffsetForCursorLocation(editor.getViewer());
				final Pair peek = queue.peek();
				if (peek == null || peek.offset != offset || peek.rep != activeRepresentation) {
//					System.out.println(String.format("Scheduling offset %s, %s after %s", offset, activeRepresentation, peek));
					queue.offer(new Pair(offset, activeRepresentation));
				} else {
					//System.out.println("Skipping redundant offset " + offset);
				}
			}
		};
		
		private TextPresentation textPresentation;

		public TLACoveragePainter(TLACoverageEditor editor) {
			this.editor = editor;
			
			this.painter.setPriority(Job.LONG);
			this.painter.setRule(null);
			this.painter.setSystem(true);
		}

		@Override
		public synchronized void applyTextPresentation(final TextPresentation textPresentation) {
			// Set the background color down here instead of in createSourceViewer above
			// where it is overridden by the OS's default background color.
			editor.getSourceViewer().getTextWidget().setBackground(lightGray);

			// Unregister this to not rerun the initialization again.
			editor.getViewer().removeTextPresentationListener(this);
			
			this.textPresentation = textPresentation;
			
			editor.getViewer().addTextInputListener(new ITextInputListener() {
				@Override
				public synchronized void inputDocumentChanged(IDocument oldInput, IDocument newInput) {
					editor.getViewer().removeTextInputListener(this);
					
					// Register listener to update coverage information based on mouse clicks.
					final StyledText textWidget = editor.getViewer().getTextWidget();
					textWidget.addListener(SWT.MouseDown, listener);

					// Color the editor with coverage information initially.
					queue.add(ALL);
					painter.schedule();
				}
				
				@Override
				public void inputDocumentAboutToBeChanged(IDocument oldInput, IDocument newInput) {
				}
			});
		}
	}
}
