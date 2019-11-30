package org.lamport.tla.toolbox.tool.tlc.ui.view;

import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Vector;
import java.util.regex.Pattern;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.Platform;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.ToolBarManager;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogSettings;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.dnd.Clipboard;
import org.eclipse.swt.dnd.TextTransfer;
import org.eclipse.swt.dnd.Transfer;
import org.eclipse.swt.events.MouseAdapter;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.forms.widgets.Form;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.ITextEditor;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCState;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariable;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.traceexplorer.TraceExplorerComposite;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.dialog.ErrorViewTraceFilterDialog;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.TLACoverageEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.preference.ITLCPreferenceConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.util.ExpandableSpaceReclaimer;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.RecordToSourceCoupler;
import org.lamport.tla.toolbox.tool.tlc.ui.util.TLCUIHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.FontPreferenceChangeListener;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;

import tlc2.output.MP;

/**
 * Error representation view containing the error description and the trace
 * explorer. This is the view of the error description.
 * 
 * @author Simon Zambrovski
 */
public class TLCErrorView extends ViewPart
{
	public static final String ID = "toolbox.tool.tlc.view.TLCErrorView";

	static final String JFACE_ERROR_TRACE_ID = ITLCPreferenceConstants.I_TLC_ERROR_TRACE_FONT + "_private";

	private static final SimpleDateFormat sdf = new SimpleDateFormat("MMM dd,yyyy HH:mm:ss");
	
	private static final String CELL_TEXT_PROTOTYPE = "{|qgyA!#93^<[?";

	private static final String INNER_WEIGHTS_KEY = "INNER_WEIGHTS_KEY";
	private static final String OUTER_WEIGHTS_KEY = "OUTER_WEIGHTS_KEY";
	private static final String MID_WEIGHTS_KEY = "MID_WEIGHTS_KEY";
  
	private static final String SYNCED_TRAVERSAL_KEY = "SYNCED_TRAVERSAL_KEY";

    private static final String NO_VALUE_VIEWER_TEXT
			= "\u2022 Select a line in Error Trace to show its value here.\n"
				+ "\u2022 Double-click on a line to go to corresponding action in spec \u2014 "
				+ "or while holding down " + (Platform.getOS().equals(Platform.OS_MACOSX) ? "\u2318" : "CTRL")
				+ " to go to the original PlusCal code, if present.\n"
				+ "\u2022 Click on a variable while holding down ALT to hide the variable from view.\n"
				+ "\u2022 Right-click on a location row for a context menu.";

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
        return new Document(NO_VALUE_VIEWER_TEXT);
    }
    
    private enum FilterType {
    	NONE, VARIABLES, MODIFIED_VALUES_ALL_FRAMES, MODIFIED_VALUES_MODIFIED_FRAMES;
    }
    
    
    private int numberOfStatesToShow;

    private FormToolkit toolkit;
    private Form form;

    private SourceViewer errorViewer;
    private ErrorTraceTreeViewer errorTraceTreeViewer;
    private RecordToSourceCoupler stackTraceActionListener;
    private SyncStackTraversal syncStackTraversalAction;
    private Button valueReflectsFiltering;
    private SourceViewer valueViewer;
    private ModelEditor modelEditor;
    private TraceExplorerComposite traceExplorerComposite;
    
    private TLCError unfilteredInput;
    private final HashMap<TLCState, Integer> filteredStateIndexMap;
    private FilterErrorTrace filterErrorTraceAction;
    private Set<TLCVariable> currentErrorTraceFilterSet;
    
    @SuppressWarnings("unused")  // held onto for a nicer object graph
	private ExpandableSpaceReclaimer spaceReclaimer;

    // listener on changes to the tlc output font preference
    private FontPreferenceChangeListener outputFontChangeListener;

	public TLCErrorView() {
		numberOfStatesToShow = TLCUIActivator.getDefault().getPreferenceStore()
				.getInt(ITLCPreferenceConstants.I_TLC_TRACE_MAX_SHOW_ERRORS);
        
        currentErrorTraceFilterSet = new HashSet<>();
        
        filteredStateIndexMap = new HashMap<>();
	}
    
    /**
     * Clears the view
     */
	public void clear() {
        errorViewer.setDocument(EMPTY_DOCUMENT());
        setTraceInput(new TLCError(), true);
        traceExplorerComposite.getTableViewer().setInput(new Vector<Formula>());
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
    protected void fill(Model model, List<TLCError> problems, final List<String> serializedInput)
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

            final IDocument document = errorViewer.getDocument();
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
             * seconds, so it is important to not reset the trace if it is not necessary.
             */
            final TLCError oldTrace = errorTraceTreeViewer.getCurrentTrace();
            final boolean isNewTrace = (trace != null) && (oldTrace != null) && !(trace == oldTrace);
            // update the trace information
            if (isNewTrace)
            {
                this.setTraceInput(trace, true);
            }
            if (model.isSnapshot()) {
            	final String date = sdf.format(model.getSnapshotTimeStamp());
            	this.form.setText(model.getSnapshotFor().getName() + " (" + date + ")");
            } else {
            	this.form.setText(model.getName());
            }

        } else
        {
            clear();
        }
        // TODO Check if a run of the trace explorer produced no errors. This would be a bug.
        
        traceExplorerComposite.changeButtonEnablement();
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
        final Display display = parent.getDisplay();
		toolkit = new FormToolkit(display);
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
            public void mouseUp(final MouseEvent e) { }

			public void mouseDown(final MouseEvent e) {
                final Set<Class<? extends ITextEditor>> blacklist = new HashSet<>();
                blacklist.add(TLACoverageEditor.class);
                TLCUIHelper.openTLCLocationHyperlink(text, e, modelEditor.getModel(), blacklist);
            }

            public void mouseDoubleClick(final MouseEvent e) { }
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
        
        final SashForm middleSashForm = new SashForm(belowErrorViewerComposite, SWT.VERTICAL);
        toolkit.adapt(middleSashForm);

        gd = new GridData(SWT.FILL, SWT.FILL, true, true);

        middleSashForm.setLayoutData(gd);

        traceExplorerComposite = new TraceExplorerComposite(middleSashForm, "Error-Trace Exploration",
                "Expressions to be evaluated at each state of the trace - drag to re-order.", toolkit, this);

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
        Section errorTraceSection = toolkit.createSection(middleSashForm, Section.TITLE_BAR);
        errorTraceSection.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
        errorTraceSection.setLayout(new GridLayout(1, true));
        errorTraceSection.setText("Error-Trace");

        // must create the client area for the section
        Composite errorTraceSectionClientArea = toolkit.createComposite(errorTraceSection);
        errorTraceSectionClientArea.setLayout(new GridLayout(1, true));
        errorTraceSection.setClient(errorTraceSectionClientArea);
        
        spaceReclaimer = new ExpandableSpaceReclaimer(traceExplorerComposite.getSection(), middleSashForm);
        
        final SashForm sashForm = new SashForm(errorTraceSectionClientArea, SWT.VERTICAL);
        toolkit.adapt(sashForm);

        gd = new GridData(SWT.FILL, SWT.FILL, true, true);

        sashForm.setLayoutData(gd);

        Tree tree = toolkit.createTree(sashForm, SWT.V_SCROLL | SWT.BORDER | SWT.FULL_SELECTION | SWT.MULTI
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
        tree.addListener(SWT.MeasureItem, (event) -> {
        	final Font originalFont = event.gc.getFont();
        	
        	event.gc.setFont(JFaceResources.getFontRegistry().getBold(JFACE_ERROR_TRACE_ID));
        	// we add 2 because SWT doesn't seem to calculate the height correctly, regardless of the prototype
        	final int height = event.gc.stringExtent(CELL_TEXT_PROTOTYPE).y + 2;
        	event.height = height;
        	
        	event.gc.setFont(originalFont);
        });

        errorTraceTreeViewer = new ErrorTraceTreeViewer(tree, modelEditor);
        getSite().setSelectionProvider(errorTraceTreeViewer.getTreeViewer());

        
        final Set<Class<? extends ITextEditor>> blacklist = new HashSet<>();
        blacklist.add(TLACoverageEditor.class);
		stackTraceActionListener = new RecordToSourceCoupler(errorTraceTreeViewer.getTreeViewer(), blacklist, this,
				RecordToSourceCoupler.FocusRetentionPolicy.ARROW_KEY_TRAVERSAL);
		tree.addMouseListener(stackTraceActionListener);
		tree.addKeyListener(stackTraceActionListener);
		tree.addDisposeListener((event) -> {
			final IDialogSettings ids = Activator.getDefault().getDialogSettings();
			ids.put(SYNCED_TRAVERSAL_KEY, syncStackTraversalAction.isChecked());
        });
		tree.addMouseListener(new MouseAdapter() {
        	@Override
        	public void mouseUp(final MouseEvent event) {
        		if ((event.stateMask & SWT.ALT) != 0) {
        			final TreeViewer treeViewer = errorTraceTreeViewer.getTreeViewer();
        			final ISelection is = treeViewer.getSelection();
        			if ((is != null) && !is.isEmpty() && (is instanceof StructuredSelection)) {
        				final Object selection = ((StructuredSelection)is).getFirstElement();
        				
        				if (selection instanceof TLCVariable) {
        					if (filterErrorTraceAction.isChecked()) {
        						addVariableFamilyToFiltering((TLCVariable)selection);
        					} else {
        						currentErrorTraceFilterSet.clear();
        						addVariableFamilyToFiltering((TLCVariable)selection);
								filterErrorTraceAction.setChecked(true);
        					}
        					
        					performVariableViewPopulation(EnumSet.of(FilterType.VARIABLES));
        				}
        			}
        		}
        	}
        });
        
        // Make it possible to expand and collapse the error trace with the push of a button.
		final ToolBarManager toolBarManager = new ToolBarManager(SWT.FLAT);
		final ToolBar toolbar = toolBarManager.createControl(errorTraceSection);
		final ShiftClickAction action = new ShiftClickAction(
				"Toggle between expand and collapse all (Shift+Click to restore the default two-level expansion)",
				TLCUIActivator.getImageDescriptor("icons/elcl16/toggle_expand_state.png"), display) {
			@Override
			void runWithKey(final boolean pressed) {
    			final TreeViewer treeViewer = errorTraceTreeViewer.getTreeViewer();
				if (pressed) {
					// expandAll() followed by expandToLevel(2) requires us
					// to collapse the viewer first.
					treeViewer.collapseAll();
					treeViewer.expandToLevel(2);
				} else {
					final Object[] expandedElements = treeViewer.getExpandedElements();
					if (expandedElements.length == 0) {
						treeViewer.expandAll();
					} else {
						treeViewer.collapseAll();
					}
				}
			}
		};
		toolBarManager.add(new ExportErrorTrace2Clipboard(display));
		filterErrorTraceAction = new FilterErrorTrace();
		toolBarManager.add(filterErrorTraceAction);
		toolBarManager.add(action);
		syncStackTraversalAction = new SyncStackTraversal();
		toolBarManager.add(syncStackTraversalAction);
		toolBarManager.update(true);
		errorTraceSection.setTextClient(toolbar);

		errorTraceTreeViewer.getTreeViewer().addSelectionChangedListener((event) -> {
			handleValueViewerUpdate((IStructuredSelection)event.getSelection());
        });

		final Composite valueViewerComposite = new Composite(sashForm, SWT.NONE);
		final GridLayout gl = new GridLayout(1, false);
		gl.marginHeight = 0;
		gl.marginWidth = 0;
		gl.verticalSpacing = 3;
		valueViewerComposite.setLayout(gl);
		gd = new GridData();
		gd.horizontalAlignment = SWT.LEFT;
		gd.verticalAlignment = SWT.TOP;
		gd.grabExcessHorizontalSpace = true;
		valueViewerComposite.setLayoutData(gd);
		
		valueReflectsFiltering = new Button(valueViewerComposite, SWT.CHECK);
		valueReflectsFiltering.setText("Reflect filtering");
		valueReflectsFiltering.setSelection(true);
		valueReflectsFiltering.addSelectionListener(new SelectionListener() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				handleValueViewerUpdate((IStructuredSelection)errorTraceTreeViewer.getTreeViewer().getSelection());
			}
			@Override
			public void widgetDefaultSelected(SelectionEvent e) { }
		});
		gd = new GridData();
		gd.horizontalAlignment = SWT.RIGHT;
		gd.verticalAlignment = SWT.TOP;
		gd.exclude = true;
		valueReflectsFiltering.setLayoutData(gd);
		valueReflectsFiltering.setVisible(false);
		
        /* Horizontal scroll bar added by LL on 26 Aug 2009 */
        valueViewer = FormHelper.createFormsSourceViewer(toolkit, valueViewerComposite,
        												 (SWT.V_SCROLL | SWT.H_SCROLL | SWT.MULTI | SWT.BORDER));
        valueViewer.setEditable(false);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.verticalAlignment = SWT.FILL;
        gd.grabExcessVerticalSpace = true;
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
        final String midWeights = dialogSettings.get(MID_WEIGHTS_KEY);
        if (midWeights != null) {
        	middleSashForm.setWeights(stringToIntArray(midWeights));
        } else {
        	final int[] weights;
        	
        	if (traceExplorerComposite.getSection().isExpanded()) {
        		weights = new int[] {3, 7};
        	} else {
        		weights = new int[] {1, 9};
        	}
        	
            middleSashForm.setWeights(weights);
        }

        sashForm.addDisposeListener((event) -> {
			final IDialogSettings ids = Activator.getDefault().getDialogSettings();
			ids.put(INNER_WEIGHTS_KEY, Arrays.toString(sashForm.getWeights()));
        });
        outerSashForm.addDisposeListener((event) -> {
			final IDialogSettings ids = Activator.getDefault().getDialogSettings();
			ids.put(OUTER_WEIGHTS_KEY, Arrays.toString(outerSashForm.getWeights()));
        });
        middleSashForm.addDisposeListener((event) -> {
			final IDialogSettings ids = Activator.getDefault().getDialogSettings();
			ids.put(MID_WEIGHTS_KEY, Arrays.toString(middleSashForm.getWeights()));
        });
        
        form.getToolBarManager().add(new HelpAction());
        form.getToolBarManager().update(true);

        // init
        clear();

        // add listeners to the preference store to react when the fonts are changed
        Vector<Control> controls = new Vector<>();
        controls.add(errorViewer.getControl());
        outputFontChangeListener = new FontPreferenceChangeListener(controls, ITLCPreferenceConstants.I_TLC_OUTPUT_FONT);
        JFaceResources.getFontRegistry().addListener(outputFontChangeListener);
		
        TLCUIHelper.setHelp(parent, IHelpConstants.TLC_ERROR_VIEW);
    }
    
    private void handleValueViewerUpdate(final IStructuredSelection structuredSelection) {
		if (!structuredSelection.isEmpty()) {
			// Set selection to the selected element (or the first if there are multiple
			// selections), and show its string representation in the value viewer (the lower sub-window).
			final Object selection = structuredSelection.getFirstElement();
			if (selection instanceof TLCState) {
				final TLCState state;
				if ((filteredStateIndexMap.size() != 0) && !valueReflectsFiltering.getSelection()) {
					final Integer index = filteredStateIndexMap.get(selection);
					
					if (index != null) {
						state = unfilteredInput.getStates(TLCError.Length.ALL).get(index.intValue());
					} else {
						TLCUIActivator.getDefault().logWarning("Could not find mapped index for state.");
						
						state = (TLCState) selection;
					}
				} else {
					state = (TLCState) selection;
				}
				valueViewer.setDocument(new Document(state.getConjunctiveDescription(true)));
			} else {
				valueViewer.setDocument(new Document(selection.toString()));
			}
		} else {
			valueViewer.setDocument(NO_VALUE_DOCUMENT());
		}
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

	public void dispose() {
		JFaceResources.getFontRegistry().removeListener(outputFontChangeListener);
        
        errorTraceTreeViewer.dispose();
        
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
		updateErrorView(modelEditor);
	}

    /**
     * Display the errors in the view, or hides the view if no errors
     * Displays data from the most recent trace explorer run for config
     * iff {@link ModelHelper#isOriginalTraceShown(ILaunchConfiguration)} is false.
     */
    public static void updateErrorView(final ModelEditor associatedModelEditor) {
    	updateErrorView(associatedModelEditor, true);
    }

	public static void updateErrorView(final ModelEditor associatedModelEditor, final boolean openErrorView) {
		if (associatedModelEditor == null) {
			return;
		}
		final Model model = associatedModelEditor.getModel();
		final boolean isTraceExplorerUpdate = !model.isOriginalTraceShown();

		final TLCModelLaunchDataProvider provider;
		if (isTraceExplorerUpdate) {
			provider = TLCOutputSourceRegistry.getTraceExploreSourceRegistry().getProvider(model);
		} else {
			provider = TLCOutputSourceRegistry.getModelCheckSourceRegistry().getProvider(model);
		}

		if (provider == null) {
			return;
		}
		
		updateErrorView(provider, associatedModelEditor, openErrorView);
	}
    
	public static void updateErrorView(final TLCModelLaunchDataProvider provider, final ModelEditor associatedModelEditor,
			final boolean openErrorView) {
        final TLCErrorView errorView;
		if ((provider.getErrors().size() > 0) && openErrorView) {
       		errorView = (TLCErrorView) UIHelper.openView(TLCErrorView.ID);
		} else {
            errorView = (TLCErrorView) UIHelper.findView(TLCErrorView.ID);
        }
		
		if (errorView != null) {
			errorView.setModelEditor(associatedModelEditor);

            final List<String> serializedInput = associatedModelEditor.getModel().getTraceExplorerExpressions();
            // fill the name and the errors
			errorView.fill(provider.getModel(), provider.getErrors(), serializedInput);

			if (provider.getErrors().size() == 0) {
                errorView.hide();
            }
        }
    }

	public TLCError getTrace() {
		if (errorTraceTreeViewer == null) {
			return null;
		}
		return errorTraceTreeViewer.getCurrentTrace();
	}

	public Model getModel() {
		return modelEditor.getModel();
	}
	
	private void setModelEditor(final ModelEditor associatedModelEditor) {
		modelEditor = associatedModelEditor;
		if (errorTraceTreeViewer != null) {
			errorTraceTreeViewer.setModelEditor(associatedModelEditor);
		}
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
	void setTraceInput(final TLCError error, final boolean isNew) {
		if (isNew) {
			unfilteredInput = error;
		}
		
		// If itemCount is large (>10.000 items), the underlying OS window
		// toolkit can be slow. As a possible fix, look into
		// http://www.eclipse.org/nattable/. For background, read
		// https://bugs.eclipse.org/bugs/show_bug.cgi?id=129457#c27
    	error.restrictTraceTo(numberOfStatesToShow);
    	final TreeViewer treeViewer = errorTraceTreeViewer.getTreeViewer();
    	treeViewer.getTree().setItemCount(error.getTraceSize() + (error.isTraceRestricted() ? 1 : 0));
    	treeViewer.setInput(error);
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
        	treeViewer.expandToLevel(level + 1); // viewer counts root node. 
        }
        if (!error.isTraceEmpty())
        {
            valueViewer.setDocument(NO_VALUE_DOCUMENT());
        } else
        {
            valueViewer.setDocument(EMPTY_DOCUMENT());
        }
    }

	public void setOriginalTraceShown(final boolean b) {
		modelEditor.getModel().setOriginalTraceShown(b);
	}
	
	TreeViewer getViewer() {
		return errorTraceTreeViewer.getTreeViewer();
	}
	
	private void addVariableFamilyToFiltering(final TLCVariable protoVariable) {
		for (final TLCState state : unfilteredInput.getStates(TLCError.Length.ALL)) {
			for (final TLCVariable variable : state.getVariablesAsList()) {
				if (protoVariable.representsTheSameAs(variable)) {
					currentErrorTraceFilterSet.add(variable);
				}
			}
		}
	}
	
	private void performVariableViewPopulation(final EnumSet<FilterType> filters) {
        filteredStateIndexMap.clear();
		if (filters.contains(FilterType.NONE)) {
			setTraceInput(unfilteredInput, false);
			final GridData gd = (GridData)valueReflectsFiltering.getLayoutData();
			gd.exclude = true;
			valueReflectsFiltering.setLayoutData(gd);
			valueReflectsFiltering.setVisible(false);
		} else {
			final TLCError filtered = unfilteredInput.clone();
			
			final GridData gd = (GridData)valueReflectsFiltering.getLayoutData();
			gd.exclude = false;
			valueReflectsFiltering.setLayoutData(gd);
			valueReflectsFiltering.setVisible(true);
			if (filters.contains(FilterType.VARIABLES) && (currentErrorTraceFilterSet.size() > 0)) {
				// It would be much nicer (from both a time and space perspective) were there a veto-ing
				//		ability provided by TableViewer - like "vetoRow(Object element)". Alas, there is not and
				//		so we do this clone and filter of the input data.
				int index = 0;
				for (final TLCState filteredState : filtered.getStates(TLCError.Length.ALL)) {
					final List<TLCVariable> variables = filteredState.getVariablesAsList();
					final ArrayList<TLCVariable> removals = new ArrayList<>();
					
					for (final TLCVariable variable : variables) {
						for (final TLCVariable filterVariable : currentErrorTraceFilterSet) {
							if (filterVariable.representsTheSameAs(variable)) {
								removals.add(variable);
								break;
							}
						}
					}
					
					variables.removeAll(removals);
					
					filteredStateIndexMap.put(filteredState, new Integer(index));
					index++;
				}
			}

			if (filters.contains(FilterType.MODIFIED_VALUES_MODIFIED_FRAMES)) {
				final ArrayList<TLCState> emptyStates = new ArrayList<>();
				
				filteredStateIndexMap.clear();
				int index = 0;
				for (final TLCState state : filtered.getStates(TLCError.Length.ALL)) {
					final List<TLCVariable> variables = state.getVariablesAsList();
					final ArrayList<TLCVariable> removals = new ArrayList<>();
					
					for (final TLCVariable variable : variables) {
						if (!variable.isChanged()) {
							removals.add(variable);
						}
					}
					
					variables.removeAll(removals);
					if (variables.size() == 0) {
						emptyStates.add(state);
					} else {
						filteredStateIndexMap.put(state, new Integer(index));
					}
					
					index++;
				}
				
				filtered.removeStates(emptyStates);
			} else if (filters.contains(FilterType.MODIFIED_VALUES_ALL_FRAMES)) {
				final Set<TLCVariable> changedVariables = new HashSet<>();
				
				for (final TLCState state : filtered.getStates(TLCError.Length.ALL)) {
					final List<TLCVariable> variables = state.getVariablesAsList();
					
					for (final TLCVariable variable : variables) {
						if (variable.isChanged()) {
							changedVariables.add(variable);
						}
					}
				}
				
				filteredStateIndexMap.clear();
				int index = 0;
				for (final TLCState filteredState : filtered.getStates(TLCError.Length.ALL)) {
					final List<TLCVariable> variables = filteredState.getVariablesAsList();
					
					variables.retainAll(changedVariables);
					
					filteredStateIndexMap.put(filteredState, new Integer(index));
					index++;
				}
			}
			
			setTraceInput(filtered, false);
		}
		valueReflectsFiltering.getParent().layout(true, true);
	}
	
	
	private class SyncStackTraversal extends Action {
		SyncStackTraversal() {
			super("Sync traversing of the stack trace by arrow keys to the editor.", AS_CHECK_BOX);
			
			final ImageDescriptor id = PlatformUI.getWorkbench().getSharedImages()
					.getImageDescriptor(ISharedImages.IMG_ELCL_SYNCED);
			setImageDescriptor(id);
			
	        final boolean enabled = Activator.getDefault().getDialogSettings().getBoolean(SYNCED_TRAVERSAL_KEY);
	        setChecked(enabled);
	        
	        run();
		}

	    /**
	     * {@inheritDoc}
	     */
		@Override
		public void run() {
			final int value = isChecked()
					? (RecordToSourceCoupler.OBSERVE_ARROW_KEY | RecordToSourceCoupler.OBSERVE_SINGLE_CLICK)
					: RecordToSourceCoupler.OBSERVE_DEFAULT;

			stackTraceActionListener.setNonDefaultObservables(value);
		}
	}
	
	
	private class FilterErrorTrace extends Action {
		private static final String DEFAULT_TOOL_TIP_TEXT
					= "Click to select variables and expressions to omit from the trace display; "
									+ "ALT-click on an individual item below to omit it immediately.";
		private static final String SELECTED_TOOL_TIP_TEXT = "Click to display all variables and expressions.";
		
		FilterErrorTrace() {
			super("Filter the displayed variables and expressions", AS_CHECK_BOX);
			
			final ImageDescriptor id = TLCUIActivator.getImageDescriptor("icons/elcl16/trace_filter.png");
			setImageDescriptor(id);
			
			setToolTipText(DEFAULT_TOOL_TIP_TEXT);
		}
		
	    /**
	     * {@inheritDoc}
	     */
		@Override
		public void setChecked(final boolean flag) {
			super.setChecked(flag);
			
			setToolTipText(SELECTED_TOOL_TIP_TEXT);
		}
		
	    /**
	     * {@inheritDoc}
	     */
		@Override
		public void run() {
			if (isChecked()) {
				setToolTipText(SELECTED_TOOL_TIP_TEXT);
			} else {
				setToolTipText(DEFAULT_TOOL_TIP_TEXT);
			}
			
			final TLCError trace = errorTraceTreeViewer.getCurrentTrace();
			final List<TLCState> states = trace.getStates();
			
			if (states.size() == 0) {
				return;
			}
			
			if (isChecked()) {
				final Shell s = PlatformUI.getWorkbench().getDisplay().getActiveShell();
				final TLCState state = states.get(0);
				final ErrorViewTraceFilterDialog dialog = new ErrorViewTraceFilterDialog(s, state.getVariablesAsList());

				dialog.setSelection(currentErrorTraceFilterSet);
				if (dialog.open() == Window.OK) { // (Currently can only ever be Windows.OK)
					currentErrorTraceFilterSet = dialog.getSelection();
					
					final ErrorViewTraceFilterDialog.MutatedFilter mutated = dialog.getMutatedFilterSelection();
					
					if (ErrorViewTraceFilterDialog.MutatedFilter.NO_FILTER.equals(mutated)) {
						performVariableViewPopulation(EnumSet.of(FilterType.VARIABLES));
					} else {
						final FilterType filterType;
						
						switch (mutated) {
							case CHANGED_ALL_FRAMES:
								filterType = FilterType.MODIFIED_VALUES_ALL_FRAMES;
								break;
							default:
								filterType = FilterType.MODIFIED_VALUES_MODIFIED_FRAMES;
								break;
						}
						
						performVariableViewPopulation(EnumSet.of(FilterType.VARIABLES, filterType));
					}
				}
			} else {
				performVariableViewPopulation(EnumSet.of(FilterType.NONE));
			}
		}
	}	
	
	
	private static abstract class ShiftClickAction extends Action implements Listener {
		private boolean holdDown = false;

		public ShiftClickAction(final String text, final ImageDescriptor imageDescriptor, final Display display) {
			super(text, imageDescriptor);
			display.addFilter(SWT.KeyDown, this);
			display.addFilter(SWT.KeyUp, this);
		}
		
		public ShiftClickAction(final String text, final int style, final Display display) {
			super(text, style);
			display.addFilter(SWT.KeyDown, this);
			display.addFilter(SWT.KeyUp, this);
		}

		@Override
		public void runWithEvent(Event event) {
			runWithKey(holdDown);
		}

		abstract void runWithKey(boolean shiftPressed);

		@Override
		public void handleEvent(Event event) {
			if (event.keyCode == SWT.SHIFT) {
				if (event.stateMask == SWT.SHIFT) {
					holdDown = false;
				} else if (event.stateMask == SWT.NONE){
					holdDown = true;
				}
			}
		}
	}
	
	
	private class ExportErrorTrace2Clipboard extends ShiftClickAction implements ISelectionChangedListener {
		private static final String DEFAULT_TOOL_TIP_TEXT
			= "Click to export error-trace to clipboard as\nsequence of records. "
				+ "Shift-click to \nomit the action's position (_TEPosition), \nname, and location.";
		
		
		private final Display display;
		
		ExportErrorTrace2Clipboard(final Display display) {
			super("Export the error-trace to the OS clipboard.", AS_PUSH_BUTTON, display);
			this.display = display;
			
			errorTraceTreeViewer.getTreeViewer().addSelectionChangedListener(this);
			
			setImageDescriptor(TLCUIActivator
					.getImageDescriptor("platform:/plugin/org.eclipse.ui.ide/icons/full/etool16/export_wiz.png"));
			
			setToolTipText(DEFAULT_TOOL_TIP_TEXT);
		}
		
		/* Disable export when variables are part of the selection */
		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			// it seems impossible this could ever be null since we treat it as non-null in the constructor.
			if (errorTraceTreeViewer == null) {
				this.setEnabled(false);
			}
			this.setEnabled(errorTraceTreeViewer.getCurrentTrace().hasTrace());
		}
		
		@Override
		public void runWithKey(final boolean excludeActionHeader) {
			// it seems impossible this could ever be null since we treat it as non-null in the constructor.
			if (errorTraceTreeViewer == null) {
				return;
			}
			final TLCError trace = errorTraceTreeViewer.getCurrentTrace();
			if (!trace.hasTrace()) {
				// safeguard in addition to isEnabled 
				return;
			}

			final Clipboard clipboard = new Clipboard(display);
			clipboard.setContents(new Object[] { trace.toSequenceOfRecords(!excludeActionHeader) },
					new Transfer[] { TextTransfer.getInstance() });
			clipboard.dispose();
		}
	}	
}
