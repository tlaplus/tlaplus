package org.lamport.tla.toolbox.tool.tlc.ui.view;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Vector;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Pattern;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogSettings;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.CellLabelProvider;
import org.eclipse.jface.viewers.ColumnViewerToolTipSupport;
import org.eclipse.jface.viewers.ILazyTreeContentProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.TreeViewerColumn;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerCell;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.ControlAdapter;
import org.eclipse.swt.events.ControlEvent;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.ScrollBar;
import org.eclipse.swt.widgets.Scrollable;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.ui.forms.widgets.Form;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.part.ViewPart;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCFcnElementVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCFunctionVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCMultiVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCNamedVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCRecordVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCSequenceVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCSetVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCSimpleVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCState;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariable;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.traceexplorer.TraceExplorerComposite;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.preference.ITLCPreferenceConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.util.ActionClickListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.ActionClickListener.LoaderTLCState;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.TLCUIHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.FontPreferenceChangeListener;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.st.Location;
import tlc2.output.MP;

/**
 * Error representation view containing the error description and the trace
 * explorer. This is the view of the error description.
 * 
 * @author Simon Zambrovski
 */
public class TLCErrorView extends ViewPart
{
	
	private static final String INNER_WEIGHTS_KEY = "INNER_WEIGHTS_KEY";
	private static final String OUTER_WEIGHTS_KEY = "OUTER_WEIGHTS_KEY";

	public static final String ID = "toolbox.tool.tlc.view.TLCErrorView";

    /**
     * This is the pattern of an error message resulting from evaluating the constant
     * expression entered in the expression field by the user.
     */
    private static final Pattern CONSTANT_EXPRESSION_ERROR_PATTERN = Pattern.compile("Evaluating assumption PrintT\\("
            + TLCModelLaunchDataProvider.CONSTANT_EXPRESSION_OUTPUT_PATTERN.toString() + "\\)", Pattern.DOTALL);


    private static final IDocument EMPTY_DOCUMENT()
    {
        return new Document("No error information");
    }

    private static final IDocument NO_VALUE_DOCUMENT()
    {
        return new Document("Select line in Error Trace to show its value here.");
    }
    
    private int numberOfStatesToShow;

    private FormToolkit toolkit;
    private Form form;

    private SourceViewer errorViewer;
    private TreeViewer variableViewer;
    private SourceViewer valueViewer;
    private Model model;
    private TraceExplorerComposite traceExplorerComposite;

    // listener on changes to the tlc output font preference
    private FontPreferenceChangeListener fontChangeListener;

	public TLCErrorView() {
		numberOfStatesToShow = TLCUIActivator.getDefault().getPreferenceStore()
				.getInt(ITLCPreferenceConstants.I_TLC_TRACE_MAX_SHOW_ERRORS);
	}
    
    /**
     * Clears the view
     */
    public void clear()
    {
        errorViewer.setDocument(EMPTY_DOCUMENT());
        setTraceInput(new TLCError());
        traceExplorerComposite.getTableViewer().setInput(new Vector<TLCState>());
        traceExplorerComposite.changeExploreEnablement(false);
        valueViewer.setInput(EMPTY_DOCUMENT());
    }

    /**
     * Fill data into the view
     * 
     * This includes loading expressions into the trace explorer table.
     * 
     * @param modelName
     *            name of the model displayed in the view title section
     * @param problems
     *            a list of {@link TLCError} objects representing the errors.
     */
    protected void fill(String modelName, List<TLCError> problems, final List<String> serializedInput)
    {
        /*
		 * Fill the trace explorer expression table with expressions saved in
		 * the config.
         * 
		 * Setting the input of the trace explorer composite table viewer to an
		 * empty vector is done to avoid adding duplicates.
         * 
		 * FormHelper.setSerializedInput adds the elements from the config to
		 * the table viewer.
         */
		traceExplorerComposite.getTableViewer().setInput(new Vector<Formula>());
		FormHelper.setSerializedInput(traceExplorerComposite.getTableViewer(), serializedInput);

        // if there are errors
		TLCError trace = null;
        if (problems != null && !problems.isEmpty())
        {
            StringBuffer buffer = new StringBuffer();
            // iterate over the errors
            for (int i = 0; i < problems.size(); i++)
            {
                TLCError error = problems.get(i);

                appendError(buffer, error);

                // read out the trace if any
                if (error.hasTrace())
                {
                    Assert.isTrue(trace == null, "Two traces are provided. Unexpected. This is a bug");
                    trace = error;
                    }
                }
            if (trace == null)
            {
            	trace = new TLCError();
            }

            IDocument document = errorViewer.getDocument();
            try
            {
                document.replace(0, document.getLength(), buffer.toString());
                TLCUIHelper.setTLCLocationHyperlinks(errorViewer.getTextWidget());
            } catch (BadLocationException e)
            {
                TLCUIActivator.getDefault().logError("Error reporting the error " + buffer.toString(), e);
            }

            /*
             * determine if trace has changed. this is important for really long
             * traces because resetting the trace input locks up the toolbox for a few
             * seconds in these cases, so it is important to not reset the trace
             * if it is not necessary
             */
            TLCError oldTrace = (TLCError) variableViewer.getInput();
            boolean isNewTrace = trace != null && oldTrace != null && !(trace == oldTrace);
            // update the trace information
            if (isNewTrace)
            {
                this.setTraceInput(trace);
                traceExplorerComposite.changeExploreEnablement(true);
            }
            this.form.setText(modelName);

        } else
        {
            clear();
        }
        // TODO Check if a run of the trace explorer produced no errors. This would be a bug.
    }

    /**
     * Hides the current view
     */
    public void hide()
    {
        getViewSite().getPage().hideView(TLCErrorView.this);
    }

	/**
     * Creates the layout and fill it with data
     */
    public void createPartControl(Composite parent)
    {

        // The following is not needed because the error viewer is no longer
        // a section of anything as of 30 Aug 2009.
        //
        // int sectionFlags = Section.DESCRIPTION | Section.TITLE_BAR
        // | Section.EXPANDED | Section.TWISTIE;
        toolkit = new FormToolkit(parent.getDisplay());
        form = toolkit.createForm(parent);
        form.setText("");
        toolkit.decorateFormHeading(form);

        GridLayout layout;
        GridData gd;
        Composite body = form.getBody();
        layout = new GridLayout(1, false);
        body.setLayout(layout);

        /*
         * The following added by LL 30 Aug 2009 to put the errorViewer and the
         * trace viewer inside a SashForm to permit the user to adjust their
         * heights.
         */
        final SashForm outerSashForm = new SashForm(body, SWT.VERTICAL);
        toolkit.adapt(outerSashForm);
        gd = new GridData(SWT.FILL, SWT.FILL, true, true);
        outerSashForm.setLayoutData(gd);

        // error section

        // On 30 Aug 2009 LL commented out the following code that put a "hider"
        // around the error viewer.
        //
        // Section section = FormHelper.createSectionComposite(outerSashForm,
        // "Error", "", toolkit, sectionFlags, null);
        // // Section section = FormHelper.createSectionComposite(body, "Error",
        // "", toolkit, sectionFlags, null);
        // gd = new GridData(SWT.FILL, SWT.FILL, true, false);
        // section.setLayoutData(gd);
        // Composite clientArea = (Composite) section.getClient();
        // layout = new GridLayout();
        // clientArea.setLayout(layout);
        //
        // errorViewer = FormHelper.createFormsOutputViewer(toolkit, clientArea,
        // SWT.V_SCROLL | SWT.MULTI);
        errorViewer = FormHelper.createFormsOutputViewer(toolkit, outerSashForm, SWT.V_SCROLL | SWT.H_SCROLL
                | SWT.MULTI | SWT.BORDER);
        gd = new GridData(SWT.FILL, SWT.FILL, true, false);
        gd.heightHint = 100;
        errorViewer.getControl().setLayoutData(gd);
        errorViewer.getControl().setFont(JFaceResources.getFont(ITLCPreferenceConstants.I_TLC_OUTPUT_FONT));

        /*
         * Add a listener to clicks in the error viewer.
         * 
         * Currently, this listener just reacts to clicks
         * on location hyperlinks.
         */
        final StyledText text = errorViewer.getTextWidget();
        text.addMouseListener(new MouseListener() {

            public void mouseUp(MouseEvent e)
            {
                // TODO Auto-generated method stub

            }

            public void mouseDown(MouseEvent e)
            {
                TLCUIHelper.openTLCLocationHyperlink(text, e, model);
            }

            public void mouseDoubleClick(MouseEvent e)
            {
                // TODO Auto-generated method stub

            }
        });

        /*
         * We want the lower part of the outer sash form to contain
         * the trace explorer expression table section and the inner sash form
         * containing the trace tree and the variable viewer.
         * Not putting the trace explorer expression table in the sash form
         * allows the sash form to expand into the space left behind when the
         * user contracts the trace explorer expression section.
         * 
         * The lower part of the outer sash form contains the composite
         * belowErrorViewerComposite which contains the trace explorer expression
         * table section and the errorTraceSection which contains the inner sash form.
         */
        Composite belowErrorViewerComposite = toolkit.createComposite(outerSashForm);
        layout = new GridLayout(1, false);
        /*
         * There is already some margin around this composite
         * when it is placed in the lower part of the outer sash form. It
         * looks bad when the additional default margin (5 pixels) is placed
         * around the left and right edges of widgets that are placed within the
         * belowErrorViewerComposite. To eliminate this default margin,
         * we set the margin width to 0.
         */
        layout.marginWidth = 0;
        belowErrorViewerComposite.setLayout(layout);

        traceExplorerComposite = new TraceExplorerComposite(belowErrorViewerComposite, "Error-Trace Exploration",
                "Enter expressions to be evaluated at each state of the trace", toolkit, this);

        // A group can be used to organize and provide a title for the inner sash form
        // but right now I think the section looks better because it looks the same
        // as the trace explorer section
        // Group lowerGroup = new Group(belowErrorViewerComposite, SWT.SHADOW_NONE);
        // lowerGroup.setLayout(new GridLayout(1, true));
        // lowerGroup.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
        // lowerGroup.setText("Error-Trace");

        /*
         * This section contains the inner sash form which contains the error trace table
         * and the variable value viewer.
         * 
         * Putting these in a section gives a them a title and logically groups them together.
         * 
         * There is no reason to make it possible to not have this in the expanded form, so the
         * only style bit is for the title bar.
         */
        Section errorTraceSection = toolkit.createSection(belowErrorViewerComposite, Section.TITLE_BAR);
        errorTraceSection.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
        errorTraceSection.setLayout(new GridLayout(1, true));
        errorTraceSection.setText("Error-Trace");

        // must create the client area for the section
        Composite errorTraceSectionClientArea = toolkit.createComposite(errorTraceSection);
        errorTraceSectionClientArea.setLayout(new GridLayout(1, true));
        errorTraceSection.setClient(errorTraceSectionClientArea);

        // Modified on 30 Aug 2009 as part of putting error viewer inside a
        // sash.
        // SashForm sashForm = new SashForm(body, SWT.VERTICAL); //
        final SashForm sashForm = new SashForm(errorTraceSectionClientArea/*belowErrorViewerComposite*/, SWT.VERTICAL);
        toolkit.adapt(sashForm);

        gd = new GridData(SWT.FILL, SWT.FILL, true, true);

        sashForm.setLayoutData(gd);

        Tree tree = toolkit.createTree(sashForm, SWT.V_SCROLL | SWT.BORDER | SWT.FULL_SELECTION | SWT.SINGLE
                | SWT.VIRTUAL);
        tree.setHeaderVisible(true);
        tree.setLinesVisible(true);

        gd = new GridData(SWT.LEFT, SWT.TOP, true, false);
        gd.minimumHeight = 300;
        // gd.minimumWidth = 300;

        // LL tried the following in attempting to fix the layout of the trace
        // viewer, but it did nothing
        // gd.grabExcessHorizontalSpace = true ;

        tree.setLayoutData(gd);

        // Initialize the trace display's resizer.
        TraceDisplayResizer resizer = new TraceDisplayResizer();
        resizer.comp = sashForm;
        resizer.tree = tree;
        
        tree.addControlListener(resizer);

        variableViewer = new TreeViewer(tree);
        final StateContentProvider provider = new StateContentProvider(variableViewer);
        variableViewer.setUseHashlookup(true);
		variableViewer.setContentProvider(provider);
        ColumnViewerToolTipSupport.enableFor(variableViewer);
        getSite().setSelectionProvider(variableViewer);

        final StateLabelProvider labelProvider = new StateLabelProvider();
		for (int i = 0; i < StateLabelProvider.COLUMN_TEXTS.length; i++) {
			final TreeViewerColumn column = new TreeViewerColumn(variableViewer, i);
			column.getColumn().setText(StateLabelProvider.COLUMN_TEXTS[i]);
			column.getColumn().setWidth(StateLabelProvider.COLUMN_WIDTH[i]);
			column.setLabelProvider(labelProvider);
			resizer.column[i] = column.getColumn(); // set up the resizer.
			column.getColumn().addSelectionListener(new SelectionAdapter() {
				public void widgetSelected(final SelectionEvent e) {
					// reverse the current trace
					final TLCError error = (TLCError) variableViewer.getInput();
					error.reverseTrace();
					// Reset the viewer's selection to the empty selection. With empty
					// selection, the subsequent refresh call does *not* invalidate the
					// StateContentProvider's lazy policy.
					// We know that the user clicked on the tree's column header
					// and the real selection is of little importance.
					variableViewer.setSelection(new ISelection() {
						public boolean isEmpty() {
							return true;
						}
					});
					variableViewer.refresh(false);
					
					// remember the order for next trace shown
					final IDialogSettings dialogSettings = Activator.getDefault().getDialogSettings();
					dialogSettings.put(TLCModelLaunchDataProvider.STATESORTORDER,
							!dialogSettings.getBoolean(TLCModelLaunchDataProvider.STATESORTORDER));
				}
			});
		}

        // I need to add a listener for size changes to column[0] to
        // detect when the user has tried to resize the individual columns.
        // The following might work, if I can figure out the real event type
        // to use.
        int eventType = SWT.Resize; // (2^25) - 1 ; // 1023; // what should this
        // be?
        resizer.column[0].addListener(eventType, resizer);

        variableViewer.getTree().addMouseListener(new ActionClickListener(variableViewer));
        variableViewer.getTree().addKeyListener(new ActionClickListener(variableViewer));

// This is working but I'm not sure we need it. ActionClickListener
// has a keystroke to collapse the viewer.        
//        // Add a right click context menu to expand and collapse all variables. 
//		final MenuManager contextMenu = new MenuManager("#ViewerMenu"); //$NON-NLS-1$
//		contextMenu.setRemoveAllWhenShown(true);
//		contextMenu.addMenuListener(new IMenuListener() {
//			@Override
//			public void menuAboutToShow(IMenuManager mgr) {
//				mgr.add(new Action("&Collapse All") {
//					public void run() {
//						variableViewer.collapseAll();
//					}
//				});
//				mgr.add(new Action("Expand to &default level") {
//					public void run() {
//						// expandAll() followed by expandToLevel(2) requires us
//						// to collapse the viewer first.
//						variableViewer.collapseAll();
//						variableViewer.expandToLevel(2);
//					}
//				});
//				mgr.add(new Action("&Expand All") {
//					public void run() {
//						variableViewer.expandAll();
//					}
//				});
//			}
//		});
//		final Menu menu = contextMenu.createContextMenu(variableViewer.getControl());
//		variableViewer.getControl().setMenu(menu);
//
        variableViewer.addSelectionChangedListener(new ISelectionChangedListener() {

            public void selectionChanged(SelectionChangedEvent event)
            {
                if (!((IStructuredSelection) event.getSelection()).isEmpty())
                {
                    // Set selection to the selected element (or the
                    // first if there are multiple
                    // selections), and show its string representation
                    // in the value viewer
                    // (the lower sub-window).
                    Object selection = ((IStructuredSelection) event.getSelection()).getFirstElement();
                    if (selection instanceof TLCState)
                    {
                        TLCState state = (TLCState) selection;
                        valueViewer.setDocument(new Document(state.getDescriptionWithTraceExpressions()));
                    } else
                    {
                        valueViewer.setDocument(new Document(selection.toString()));
                    }
                } else
                {
                    valueViewer.setDocument(NO_VALUE_DOCUMENT());
                }

            }
        });

        /* Horizontal scroll bar added by LL on 26 Aug 2009 */
        valueViewer = FormHelper.createFormsSourceViewer(toolkit, sashForm, SWT.V_SCROLL | SWT.H_SCROLL | SWT.MULTI
                | SWT.BORDER);
        valueViewer.setEditable(false);

        gd = new GridData(SWT.LEFT, SWT.TOP, true, false);
        valueViewer.getControl().setLayoutData(gd);

 
		// Restore the sash ratio from the persistent disk storage. Unfortunately it
		// doesn't support storing int[] directly, thus have to convert the string
		// representation back to an int[] manually.
		// It also sets the default ratio if the dialogsettings return null.
		// This is the case with a fresh workspace or when the dialog settings
		// have never been written before.
        final IDialogSettings dialogSettings = Activator.getDefault().getDialogSettings();
        final String innerWeights = dialogSettings.get(INNER_WEIGHTS_KEY);
        if (innerWeights != null) {
        	sashForm.setWeights(stringToIntArray(innerWeights));
        } else {
        	sashForm.setWeights(new int[] {1,1});
        }
        final String outerWeights = dialogSettings.get(OUTER_WEIGHTS_KEY);
        if (outerWeights != null) {
        	outerSashForm.setWeights(stringToIntArray(outerWeights));
        } else {
        	outerSashForm.setWeights(new int[] {1,4});
        }

        sashForm.addDisposeListener(new DisposeListener() {
			public void widgetDisposed(DisposeEvent e) {
				final IDialogSettings dialogSettings = Activator.getDefault().getDialogSettings();
		        dialogSettings.put(INNER_WEIGHTS_KEY, Arrays.toString(sashForm.getWeights()));
			}
		});
        outerSashForm.addDisposeListener(new DisposeListener() {
			public void widgetDisposed(DisposeEvent e) {
				final IDialogSettings dialogSettings = Activator.getDefault().getDialogSettings();
		        dialogSettings.put(OUTER_WEIGHTS_KEY, Arrays.toString(outerSashForm.getWeights()));
			}
        });
        
        form.getToolBarManager().add(new HelpAction());
        form.getToolBarManager().update(true);

        // init
        clear();

        // add a listener to the preference store to react when the font is
        // changed

        Vector<Control> controls = new Vector<Control>();
        controls.add(errorViewer.getControl());
        fontChangeListener = new FontPreferenceChangeListener(controls, ITLCPreferenceConstants.I_TLC_OUTPUT_FONT);
        JFaceResources.getFontRegistry().addListener(fontChangeListener);

        TLCUIHelper.setHelp(parent, IHelpConstants.TLC_ERROR_VIEW);

    }
    
	private int[] stringToIntArray(final String str) {
		final String[] strings = str.replace("[", "").replace("]", "").split(", ");
		int result[] = new int[strings.length];
		for (int i = 0; i < result.length; i++) {
			result[i] = Integer.parseInt(strings[i]);
		}
		return result;
	}

    public void setFocus()
    {
        form.setFocus();
    }

    public void dispose()
    {
        JFaceResources.getFontRegistry().removeListener(fontChangeListener);
        toolkit.dispose();
        super.dispose();
    }

    /**
     * Appends the error description to the buffer.
     * 
     * This method filters and replaces strings in TLC's
     * output that we don't want the user to see.
     * 
     * Currently, it filters out the starting and ending
     * tags and replaces error messages resulting from
     * evaluating the constant expression field with something
     * more sensible.
     * 
     * @param buffer
     *            string buffer to append the error description to
     * @param error
     *            error object
     */
    private static void appendError(StringBuffer buffer, TLCError error)
    {
        String message = error.getMessage();
        if (message != null && !message.equals(""))
        {
            // remove start and end tags from the message
            String toAppend = message.replaceAll(MP.DELIM + MP.STARTMSG + "[0-9]{4}" + MP.COLON + "[0-9] " + MP.DELIM,
                    "");
            toAppend = toAppend.replaceAll(MP.DELIM + MP.ENDMSG + "[0-9]{4} " + MP.DELIM, "");
            // Replace error messages resulting from evaluating the constant
            // expression field with something more sensible.
            toAppend = CONSTANT_EXPRESSION_ERROR_PATTERN.matcher(toAppend).replaceAll(
                    "The `Evaluate Constant Expression� section�s evaluation");
            buffer.append(toAppend).append("\n");
        }
        TLCError cause = error.getCause();
        // look for a cause that has a message
        // that is not a substring of this error's
        // message
        // if one is found, append that error
        while (cause != null)
        {
            if (message == null || !message.contains(cause.getMessage()))
            {
                appendError(buffer, cause);
                break;
            } else
            {
                cause = cause.getCause();
            }
        }
    }

	public void updateErrorView() {
		updateErrorView(this.model);
	}

    /**
     * Display the errors in the view, or hides the view if no errors
     * Displays data from the most recent trace explorer run for config
     * iff {@link ModelHelper#isOriginalTraceShown(ILaunchConfiguration)} is false.
     * 
     * @param errors
     *            a list of {@link TLCError}
     */
    public static void updateErrorView(Model model) {
    	System.out.println(model);
    	updateErrorView(model, true);
    }

    public static void updateErrorView(Model model, boolean openErrorView)
    {
        if (model == null)
        {
            return;
        }
        boolean isTraceExplorerUpdate;
        isTraceExplorerUpdate = !model.isOriginalTraceShown();

        TLCModelLaunchDataProvider provider = null;
        if (isTraceExplorerUpdate)
        {
            provider = TLCOutputSourceRegistry.getTraceExploreSourceRegistry().getProvider(model);
        } else
        {
            provider = TLCOutputSourceRegistry.getModelCheckSourceRegistry().getProvider(model);
        }

        if (provider == null)
        {
            return;
        }
        updateErrorView(provider, model, openErrorView);
    }
    
	public static void updateErrorView(final TLCModelLaunchDataProvider provider, final Model model,
			boolean openErrorView) {
        TLCErrorView errorView;
		if (provider.getErrors().size() > 0 && openErrorView == true) {
       		errorView = (TLCErrorView) UIHelper.openView(TLCErrorView.ID);
		} else {
            errorView = (TLCErrorView) UIHelper.findView(TLCErrorView.ID);
        }
		if (errorView != null) {
            errorView.model= model;

            final List<String> serializedInput = model.getTraceExplorerExpressions();
            // fill the name and the errors
			errorView.fill(provider.getModel().getName(), provider.getErrors(),
					serializedInput);

			if (provider.getErrors().size() == 0) {
                errorView.hide();
            }
        }
    }

    /**
     * A control listener for the Provides method for resizing the columns of
     * the error trace viewer. This is to solve the problem of a bogus
     * "third column" being displayed when the window is made wider than the two
     * real columns.
     * 
     * There are two listener methods in this class: controlResized - called
     * when the tree is resized. handleEvent - called when column[0] is resized.
     * The controlResized command can change the size of column[0], which
     * triggers the calling of the handleEvent. Experimentation indicates that
     * this call of handleEvent occurs in the middle of executing the call of
     * controlResized. The boolean flag inControlResized is used to tell the
     * handleEvent method whether it was called this way or by the user resizing
     * the colulmn.
     * 
     * Note: I am assuming that the call of handleEvent that happens when
     * controlResized is resizing column[0] happens during the execution of
     * column[0].setWidth, and no funny races are possible.
     * 
     * Note that all the code here assumes that there are two columns. It needs
     * to be modified if the number of columns is changed.
     */
    static class TraceDisplayResizer extends ControlAdapter implements Listener
    {
        double firstColumnPercentageWidth = .5;

        // See comments above for meaning of the following flag.
        boolean inControlResized = false;
        Scrollable comp; // The component containing the trace display.
        TreeColumn[] column = new TreeColumn[StateLabelProvider.COLUMN_TEXTS.length];
        Tree tree;

        public void controlResized(ControlEvent e)
        {
            inControlResized = true;

            int treeWidth = computeMaximumWidthOfAllColumns();
            int firstColWidth = Math.round(Math.round(firstColumnPercentageWidth * treeWidth));
            int secondColWidth = treeWidth - firstColWidth;
            column[0].setWidth(firstColWidth);
            column[1].setWidth(secondColWidth);
            inControlResized = false;
        }

        int count = 0;

        public void handleEvent(Event event)
        {
            if (inControlResized)
            {
                return;
            }

            int treeWidth = computeMaximumWidthOfAllColumns();
            int firstColWidth = column[0].getWidth();

            if (treeWidth == 0)
            {
                return;
            }

            // the percentage that the first column will occupy
            // until controlResized is called
            // We do not want the width of either column
            // to be less than 10% of the total width
            // of the tree. Currently, the user
            // can make a column smaller than 10%, but
            // when controlResized is called, the column
            // will be enlarged to 10%. It is not very nice
            // to do the enlarging in this method. It creates
            // very choppy performance.
            double tentativefirstColPercentageWidth = (double) firstColWidth / (double) treeWidth;
            if (tentativefirstColPercentageWidth > .1 && tentativefirstColPercentageWidth < .9)
            {
                firstColumnPercentageWidth = (double) firstColWidth / (double) treeWidth;

            } else if (tentativefirstColPercentageWidth <= .1)
            {
                firstColumnPercentageWidth = .1;
            } else
            {
                firstColumnPercentageWidth = .9;
            }
            firstColWidth = Math.round(Math.round(tentativefirstColPercentageWidth * treeWidth));
            int secondColWidth = treeWidth - firstColWidth;
            column[1].setWidth(secondColWidth);
        }

        /*
         * Computes the maximum width that columns of the tree can occupy
         * without having a horizontal scrollbar.
         * 
         * This is not equal to the sash form's client area. From the client
         * area we must subtract the tree's border width. We must also subtract
         * the width of the grid lines used in the tree times the number of
         * columns because there is one grid line per column. We must subtract
         * the width of the vertical scroll bar if it is visible.
         */
        private int computeMaximumWidthOfAllColumns()
        {
            ScrollBar vBar = tree.getVerticalBar();
            boolean scrollBarShown = vBar.isVisible();
            return comp.getClientArea().width - tree.getBorderWidth() - tree.getColumnCount() * tree.getGridLineWidth()
                    - ((scrollBarShown) ? vBar.getSize().x : 0);
        }

    }

    /**
     * Content provider for the tree table
     */
    private class StateContentProvider implements ILazyTreeContentProvider {
       	
    	private final TreeViewer viewer;
		private List<TLCState> states = new ArrayList<TLCState>(0);

		public StateContentProvider(TreeViewer viewer) {
			this.viewer = viewer;
    	}

		/* (non-Javadoc)
		 * @see org.eclipse.jface.viewers.IContentProvider#dispose()
		 */
		public void dispose() {
		}

		/* (non-Javadoc)
		 * @see org.eclipse.jface.viewers.IContentProvider#inputChanged(org.eclipse.jface.viewers.Viewer, java.lang.Object, java.lang.Object)
		 */
		public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
			// Eagerly cache the list of states as it can be a sublist of the
			// complete trace. Getting the sublist in the updateElement method
			// means we obtain it over and over again for each top-level tree
			// item.
			if (newInput instanceof TLCError) {
				this.states = ((TLCError) newInput).getStates();
			} else if (newInput == null) {
				this.states = new ArrayList<TLCState>(0);
			} else {
				throw new IllegalArgumentException();
			}
		}

		/* (non-Javadoc)
		 * @see org.eclipse.jface.viewers.ILazyTreeContentProvider#updateElement(java.lang.Object, int)
		 */
		public void updateElement(Object parent, int viewerIndex) {
			if (parent instanceof TLCError) {
				final TLCError error = (TLCError) parent;
				if (error.isTraceRestricted() && viewerIndex == 0) {
					// If only a subset of the trace is shown, show a dummy item
					// at the top which can be double-clicked to load more.
					viewer.replace(parent, viewerIndex, new ActionClickListener.LoaderTLCState(viewer,
							Math.min(numberOfStatesToShow, error.getNumberOfRestrictedTraceStates()), error));
					return;
				}
				// decrease index into states by one if the viewers first element is a dummy item
				final int statesIndex = viewerIndex - (error.isTraceRestricted() ? 1 : 0);
				final TLCState child = states.get(statesIndex);
				// Diffing is supposed to be lazy and thus is done here when
				// the state is first used by the viewer. The reason why it
				// has to be lazy is to be able to efficiently handle traces
				// with hundreds or thousands of states where it would be a
				// waste to diff all state pairs even if the user is never
				// going to look at all states anyway.
				// TODO If ever comes up as a performance problem again, the
				// nested TLCVariableValues could also be diffed lazily.
           		if (statesIndex > 0) {
           			final TLCState predecessor = states.get(statesIndex - 1);
           			predecessor.diff(child);
           		}
				viewer.replace(parent, viewerIndex, child);
				if (child.getVariablesAsList().size() > 0) {
					viewer.setHasChildren(child, true);
				}
				// Lazily expand the children
				viewer.expandToLevel(child, 1);
			} else if (parent instanceof TLCState) {
				final TLCState state = (TLCState) parent;
                if ((state.isStuttering() || state.isBackToState())) {
					viewer.setChildCount(state, 0);
                } else {
                	final List<TLCVariable> variablesAsList = state.getVariablesAsList();
                	if (variablesAsList.size() > viewerIndex) {
                		final TLCVariable child = variablesAsList.get(viewerIndex);
                		viewer.replace(parent, viewerIndex, child);
                		if (child.getChildCount() > 0) {
                			viewer.setHasChildren(child, true);
                		}
                	}
                }
			} else if (parent instanceof TLCVariable
					&& ((TLCVariable) parent).getValue() instanceof TLCMultiVariableValue) {
				final TLCMultiVariableValue multiValue = (TLCMultiVariableValue) ((TLCVariable) parent).getValue();
				final TLCVariableValue child = multiValue.asList().get(viewerIndex);
				viewer.replace(parent, viewerIndex, child);
				if (child.getChildCount() > 0) {
					viewer.setHasChildren(child, true);
				}
			} else if (parent instanceof TLCVariable) {
				final TLCVariable variable = (TLCVariable) parent;
				final TLCVariableValue child = variable.getValue();
				viewer.replace(parent, viewerIndex, child);
				if (child.getChildCount() > 0) {
					viewer.setChildCount(child, child.getChildCount());
				}
			} else if (parent instanceof TLCMultiVariableValue) {
				final TLCMultiVariableValue multiValue = (TLCMultiVariableValue) parent;
				final TLCVariableValue child = multiValue.asList().get(viewerIndex);
				viewer.replace(parent, viewerIndex, child);
				if (child.getChildCount() > 0) {
					viewer.setHasChildren(child, true);
				}
			} else if (parent instanceof TLCVariableValue
					&& ((TLCVariableValue) parent).getValue() instanceof TLCMultiVariableValue) {
				final TLCMultiVariableValue multiValue = (TLCMultiVariableValue) ((TLCVariableValue) parent).getValue();
				final TLCVariableValue child = multiValue.asList().get(viewerIndex);
				viewer.replace(parent, viewerIndex, child);
				if (child.getChildCount() > 0) {
					viewer.setHasChildren(child, true);
				}
			} else {
				throw new IllegalArgumentException();
			}
		}
		
		/* (non-Javadoc)
		 * @see org.eclipse.jface.viewers.ILazyTreeContentProvider#updateChildCount(java.lang.Object, int)
		 */
		public void updateChildCount(Object element, int currentChildCount) {
			if (element instanceof TLCError) {
				final TLCError error = (TLCError) element;
				int traceSize = error.getTraceSize();
				if (traceSize != currentChildCount) {
					if (error.isTraceRestricted()) {
						viewer.setChildCount(element, traceSize + 1);
					} else {
						viewer.setChildCount(element, traceSize);
					}
				}
			} else if (element instanceof TLCState) {
				final TLCState state = (TLCState) element;
				if (((state.isStuttering() || state.isBackToState()) && currentChildCount != 0)) {
					viewer.setChildCount(element, 0);
				} else if (currentChildCount != state.getVariablesAsList().size()) {
					viewer.setChildCount(element, state.getVariablesAsList().size());
				}
			} else if (element instanceof TLCVariable) {
				final TLCVariable variable = (TLCVariable) element;
				if (currentChildCount != variable.getChildCount()) {
					viewer.setChildCount(element, variable.getChildCount());
				}
			} else if (element instanceof TLCVariableValue) {
				final TLCVariableValue value = (TLCVariableValue) element;
				if (currentChildCount != value.getChildCount()) {
					viewer.setChildCount(element, value.getChildCount());
				}
			} else {
				throw new IllegalArgumentException();
			}
		}

		/* (non-Javadoc)
		 * @see org.eclipse.jface.viewers.ILazyTreeContentProvider#getParent(java.lang.Object)
		 */
		public Object getParent(Object element) {
			return null;
		}
    }
    
    /**
     * Label provider for the tree table. Modified on 30 Aug 2009 by LL to
     * implement ITableColorProvider instead of IColorProvider. This allows
     * coloring of individual columns, not just of entire rows.
     */
    static class StateLabelProvider extends CellLabelProvider
    {
        public static final int NAME = 0;
        public static final int VALUE = 1;

        public static final int[] COLUMN_WIDTH = { 200, 200 };
        public static final String[] COLUMN_TEXTS = { "Name", "Value" };

        private final Image stateImage;
        private final Image varImage;
        private final Image recordImage;
        private final Image setImage;
        private final Image loadMoreImage;
        
        public StateLabelProvider()
        {
            stateImage = TLCUIActivator.getImageDescriptor("/icons/full/default_co.gif").createImage();
            varImage = TLCUIActivator.getImageDescriptor("/icons/full/private_co.gif").createImage();
            recordImage = TLCUIActivator.getImageDescriptor("/icons/full/brkpi_obj.gif").createImage();
            // setImage = TLCUIActivator.getImageDescriptor("/icons/full/over_co.gif").createImage();
            setImage = TLCUIActivator.getImageDescriptor("/icons/full/compare_method.gif").createImage();
            loadMoreImage = TLCUIActivator.getImageDescriptor("/icons/full/add.gif").createImage(); // other candidate is newstream_wiz.gif, nav_go.gif, debugt_obj.gif
        }

        private Image getColumnImage(Object element, int columnIndex)
        {
            if (columnIndex == NAME)
            {
            	if (element instanceof LoaderTLCState) {
            		return loadMoreImage;	
            	}
                if (element instanceof TLCState)
                {
                    return stateImage;
                } else if (element instanceof TLCVariable)
                {
                    return varImage;
                } else if (element instanceof TLCNamedVariableValue)
                {
                    return recordImage;
                } else if (element instanceof TLCFcnElementVariableValue)
                {
                    return recordImage;
                }
                return setImage; // other things appear in unordered collections
            }
            return null;
        }

        private String getColumnText(Object element, int columnIndex)
        {
            if (element instanceof TLCState)
            {
                TLCState state = (TLCState) element;

                switch (columnIndex) {
                case NAME:
                    if (state.isStuttering())
                    {
                        return "<Stuttering>";
                    } else if (state.isBackToState())
                    {
                        return "<Back to state " + state.getStateNumber() + ">";
                    }
                    return state.getLabel();
                case VALUE:
                	if (state instanceof ActionClickListener.LoaderTLCState) {
                    	return "";
                    } else {
                    	return "State (num = " + state.getStateNumber() + ")";
                    }
                    // state.toString();
                default:
                    break;
                }
            } else if (element instanceof TLCVariable)
            {
                TLCVariable var = (TLCVariable) element;
                switch (columnIndex) {
                case NAME:
                    if (var.isTraceExplorerVar())
                    {
                        return var.getSingleLineName();
                    } else
                    {
                        return var.getName();
                    }
                case VALUE:
                    return var.getValue().toSimpleString();
                    // Changed from toString by LL on 30 Aug 2009
                default:
                    break;
                }
            } else if (element instanceof TLCSetVariableValue || element instanceof TLCSequenceVariableValue
                    || element instanceof TLCSimpleVariableValue)
            {

                TLCVariableValue varValue = (TLCVariableValue) element;
                switch (columnIndex) {
                case VALUE:
                    return varValue.toString();
                case NAME:
                    return ""; // added by LL on 5 Nov 2009
                default:
                    break;
                }
            } else if (element instanceof TLCNamedVariableValue)
            {
                TLCNamedVariableValue namedValue = (TLCNamedVariableValue) element;
                switch (columnIndex) {
                case NAME:
                    return namedValue.getName();
                case VALUE:
                    return ((TLCVariableValue) namedValue.getValue()).toSimpleString();
                    // Changed from toString by LL on 30 Aug 2009
                default:
                    break;
                }
            } else if (element instanceof TLCFcnElementVariableValue)
            {
                TLCFcnElementVariableValue fcnElementValue = (TLCFcnElementVariableValue) element;
                switch (columnIndex) {
                case NAME:
                    return fcnElementValue.getFrom().toSimpleString();
                    // Changed from toString by LL on 30 Aug 2009
                case VALUE:
                    return ((TLCVariableValue) fcnElementValue.getValue()).toSimpleString();
                    // Changed from toString by LL on 30 Aug 2009
                default:
                    break;
                }
            } else if (element instanceof TLCRecordVariableValue)
            {
                TLCRecordVariableValue recordValue = (TLCRecordVariableValue) element;
                switch (columnIndex) {
                case NAME:
                    return "";
                case VALUE:
                    return recordValue.toSimpleString();
                default:
                    break;
                }
            } else if (element instanceof TLCFunctionVariableValue)
            {
                TLCFunctionVariableValue fcnValue = (TLCFunctionVariableValue) element;
                switch (columnIndex) {
                case NAME:
                    return "";
                case VALUE:
                    return fcnValue.toSimpleString();
                default:
                    break;
                }
            }

            return null;
        }

		private static final Map<String, Color> location2color = new ConcurrentHashMap<String, Color>();
		//TODO Convert to Toolbox preference once this features proves useful.
		private static final boolean coloring = Boolean.getBoolean(TLCErrorView.class.getName() + ".coloring");

        /**
         * The following method sets the background color of a row or column of
         * the table. It highlights the entire row for an added or deleted item.
         * For a changed value, only the value is highlighted.
         */
		private Color getBackground(Object element, int column) {
            if (element instanceof TLCVariable) {
				final TLCVariable var = (TLCVariable) element;
				if (var.isChanged() && column == VALUE) {
					return TLCUIActivator.getDefault().getChangedColor();
				}
			} else if (element instanceof TLCVariableValue) {
				final TLCVariableValue value = (TLCVariableValue) element;
				if (value.isChanged()) {
					if (column == VALUE) {
						return TLCUIActivator.getDefault().getChangedColor();
					}
				} else if (value.isAdded()) {
					return TLCUIActivator.getDefault().getAddedColor();
				} else if (value.isDeleted()) {
					return TLCUIActivator.getDefault().getDeletedColor();
				}
			} else if (coloring && element instanceof TLCState) {
				// Assign a color to each location to make actions in the error
				// viewer easier distinguishable.
				final TLCState state = (TLCState) element;
				Location moduleLocation = state.getModuleLocation();
				if (moduleLocation == null) {
					return null;
				}
				Color c = location2color.get(moduleLocation.toString());
				if (c == null) {
					int color = SWT.COLOR_WHITE + (2 * location2color.size());
					c = TLCUIActivator.getColor(color);
					location2color.put(state.getModuleLocation().toString(), c);
				}
				return c;
			}
			return null;
		}

        private Color getForeground(Object element, int i)
        {
            return null;
        }

        private Font getFont(Object element, int columnIndex)
        {
            if (element instanceof TLCVariable)
            {
                TLCVariable variable = (TLCVariable) element;
                if (variable.isTraceExplorerVar())
                {
                    return JFaceResources.getFontRegistry().getBold("");
                }
            } else if (element instanceof ActionClickListener.LoaderTLCState) {
                return JFaceResources.getFontRegistry().getBold("");
            }
            return null;
        }

        /* (non-Javadoc)
         * @see org.eclipse.jface.viewers.BaseLabelProvider#dispose()
         */
        public void dispose()
        {
            /*
             * Remove images
             */
            stateImage.dispose();
            varImage.dispose();
            recordImage.dispose();
            setImage.dispose();
            loadMoreImage.dispose();
           super.dispose();
        }

		/* (non-Javadoc)
		 * @see org.eclipse.jface.viewers.IToolTipProvider#getToolTipText(java.lang.Object)
		 */
		public String getToolTipText(Object element) {
			if (element instanceof LoaderTLCState) {
				return "Double-click to load more states.\nIf the number of states is large, this might take a few seconds.";
			}
			return "Click on a row to see in viewer below, double-click to go to corresponding action in spec.";
		}

		/* (non-Javadoc)
		 * @see org.eclipse.jface.viewers.CellLabelProvider#update(org.eclipse.jface.viewers.ViewerCell)
		 */
		public void update(ViewerCell cell) {
			// labels
			cell.setText(getColumnText(cell.getElement(), cell.getColumnIndex()));
			
			// images
			cell.setImage(getColumnImage(cell.getElement(), cell.getColumnIndex()));
			
			// font
			cell.setFont(getFont(cell.getElement(), cell.getColumnIndex()));
			
			// colors
			cell.setForeground(getForeground(cell.getElement(), cell.getColumnIndex()));
			cell.setBackground(getBackground(cell.getElement(), cell.getColumnIndex()));
		}
    }

	public TLCError getTrace()
    {
        if (variableViewer == null)
        {
            return null;
        }
        return (TLCError) variableViewer.getInput();
    }

	public Model getModel() {
		return model;
	}

    private class HelpAction extends Action
    {
        public HelpAction()
        {
            super("Help", JFaceResources.getImageRegistry().getDescriptor(Dialog.DLG_IMG_HELP));
            this.setDescription("Opens help");
            this.setToolTipText("Opens help for the TLC Error View.");
        }

        public void run()
        {
            UIHelper.showDynamicHelp();
        }
    }

    /**
     * Sets the input of the trace viewer to states
     * and sets the value viewer to "Select line in Error Trace to show its value here."
     * if the list of states is not empty.
     * 
     * @param states
     */
    void setTraceInput(TLCError error)
    {
		// If itemCount is large (>10.000 items), the underlying OS window
		// toolkit can be slow. As a possible fix, look into
		// http://www.eclipse.org/nattable/. For background, read
		// https://bugs.eclipse.org/bugs/show_bug.cgi?id=129457#c27
    	error.restrictTraceTo(numberOfStatesToShow);
		variableViewer.getTree().setItemCount(error.getTraceSize() + (error.isTraceRestricted() ? 1 : 0));
        variableViewer.setInput(error);
		// If the number of states in the trace is sufficiently small, eagerly
		// expand all root level items (which translates to the states
		// variables). This causes the TreeViewer to correctly determine the
		// vertical scroll bar's height. For larger number of states, we accept
		// an incorrect scroll bar height in return for lazy and thus much
		// faster item handling. I pulled the limit out of thin air, but
        // tested it on three modern (2015) laptops with Win/Mac/Linux.
        //
		// There seems to be an implementation inside the Eclipse SDK that
		// correctly handles the expanded state of a virtual tree:
		// https://bugs.eclipse.org/bugs/show_bug.cgi?id=201135
        // https://bugs.eclipse.org/bugs/show_bug.cgi?id=266189
        final int level = 1;
        if (error.getTraceSize(level) < 1000) {
        	variableViewer.expandToLevel(level + 1); // viewer counts root node. 
        }
        if (!error.isTraceEmpty())
        {
            valueViewer.setDocument(NO_VALUE_DOCUMENT());
        } else
        {
            valueViewer.setDocument(EMPTY_DOCUMENT());
        }
    }

	public void setOriginalTraceShown(boolean b) {
		this.model.setOriginalTraceShown(b);
	}
}
