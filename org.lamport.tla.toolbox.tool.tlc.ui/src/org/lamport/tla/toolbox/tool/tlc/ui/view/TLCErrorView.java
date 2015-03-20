package org.lamport.tla.toolbox.tool.tlc.ui.view;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Vector;
import java.util.regex.Pattern;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogSettings;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITableColorProvider;
import org.eclipse.jface.viewers.ITableFontProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.jface.viewers.ViewerSorter;
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
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCFcnElementVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCFunctionVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
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
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
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
 * @version $Id$
 */

public class TLCErrorView extends ViewPart
{
	private static final String INNER_WEIGHTS_KEY = "INNER_WEIGHTS_KEY";
	private static final String OUTER_WEIGHTS_KEY = "OUTER_WEIGHTS_KEY";

	public static final String ID = "toolbox.tool.tlc.view.TLCErrorView";

    private static final String TOOLTIP = "Click on a row to see in viewer, double-click to go to action in spec.";

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

    private FormToolkit toolkit;
    private Form form;

    private SourceViewer errorViewer;
    private TreeViewer variableViewer;
    private SourceViewer valueViewer;
    /**
     * a handle on the underlying configuration file representing the
     * model for which errors are currently being displayed in this view
     */
    private ILaunchConfiguration configFileHandle;
    private TraceExplorerComposite traceExplorerComposite;

    // listener on changes to the tlc output font preference
    private FontPreferenceChangeListener fontChangeListener;

    /**
     * Clears the view
     */
    public void clear()
    {
        errorViewer.setDocument(EMPTY_DOCUMENT());
        setTraceInput(Collections.EMPTY_LIST);
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
    protected void fill(String modelName, List<TLCError> problems)
    {

        try
        {
            /*
             * Fill the trace explorer expression table 
             * with expressions saved in the config.
             * 
             * Setting the input of the trace explorer composite
             * table viewer to an empty vector is done to avoid adding duplicates.
             * 
             * FormHelper.setSerializedInput adds the elements from the config
             * to the table viewer.
             */
            traceExplorerComposite.getTableViewer().setInput(new Vector());
            FormHelper.setSerializedInput(traceExplorerComposite.getTableViewer(), configFileHandle.getAttribute(
                    IModelConfigurationConstants.TRACE_EXPLORE_EXPRESSIONS, new Vector()));
        } catch (CoreException e)
        {
            TLCUIActivator.getDefault().logError("Error loading trace explorer expressions into table", e);
        }

        // if there are errors
        if (problems != null && !problems.isEmpty())
        {
            List<TLCState> states = null;
            StringBuffer buffer = new StringBuffer();
            // iterate over the errors
            for (int i = 0; i < problems.size(); i++)
            {
                TLCError error = problems.get(i);

                appendError(buffer, error);

                // read out the trace if any
                if (error.hasTrace())
                {
                    Assert.isTrue(states == null, "Two traces are provided. Unexpected. This is a bug");
                    states = error.getStates();
                }
            }
            if (states == null)
            {
                states = new LinkedList<TLCState>();
            }

            /*
             * determine if trace has changed. this is important for really long
             * traces because resetting the trace input locks up the toolbox for a few
             * seconds in these cases, so it is important to not reset the trace
             * if it is not necessary
             */
            List<TLCState> oldStates = (List<TLCState>) variableViewer.getInput();
            boolean isNewTrace = states != null && oldStates != null && !(states == oldStates);

            /*
             * Set the data structures that cause highlighting of changes in the
             * error trace.
             */
            if (isNewTrace)
            {
                setDiffInfo(states);
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

            // update the trace information
            if (isNewTrace)
            {
                this.setTraceInput(states);
                traceExplorerComposite.changeExploreEnablement(true);
            }
            if (states != null && !states.isEmpty())
            {
                variableViewer.expandToLevel(2);
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
                TLCUIHelper.openTLCLocationHyperlink(text, e, getCurrentConfigFileHandle());
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
        tree.setToolTipText(TOOLTIP);

        // Initialize the trace display's resizer.
        TraceDisplayResizer resizer = new TraceDisplayResizer();
        resizer.comp = sashForm;
        resizer.tree = tree;

        final StateViewerSorter sorter = new StateViewerSorter();
		for (int i = 0; i < StateLabelProvider.COLUMN_TEXTS.length; i++) {
			TreeColumn column = new TreeColumn(tree, SWT.LEFT);
			column.setText(StateLabelProvider.COLUMN_TEXTS[i]);
			column.setWidth(StateLabelProvider.COLUMN_WIDTH[i]);
			resizer.column[i] = column; // set up the resizer.
			column.setToolTipText(TOOLTIP);
			column.addSelectionListener(new SelectionAdapter() {
				public void widgetSelected(SelectionEvent e) {
					sorter.reverseStateSortDirection();
					variableViewer.refresh();
				}
			});
		}
        
        tree.addControlListener(resizer);

        // I need to add a listener for size changes to column[0] to
        // detect when the user has tried to resize the individual columns.
        // The following might work, if I can figure out the real event type
        // to use.
        int eventType = SWT.Resize; // (2^25) - 1 ; // 1023; // what should this
        // be?
        resizer.column[0].addListener(eventType, resizer);

        variableViewer = new TreeViewer(tree);
        variableViewer.setContentProvider(new StateContentProvider());
        variableViewer.setFilters(new ViewerFilter[] { new StateFilter() });
        variableViewer.setLabelProvider(new StateLabelProvider());
		variableViewer.setSorter(sorter);
        getSite().setSelectionProvider(variableViewer);

        variableViewer.getTree().addMouseListener(new ActionClickListener(variableViewer));

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

    /**
     * Display the errors in the view, or hides the view if no errors
     * Displays data from the most recent trace explorer run for config
     * iff {@link ModelHelper#isOriginalTraceShown(ILaunchConfiguration)} is false.
     * 
     * @param config TODO
     * @param errors
     *            a list of {@link TLCError}
     */
    public static void updateErrorView(ILaunchConfiguration config) {
    	updateErrorView(config, true);
    }

    public static void updateErrorView(ILaunchConfiguration config, boolean openErrorView)
    {

        try
        {
            if (config == null)
            {
                return;
            }
            boolean isTraceExplorerUpdate;
            isTraceExplorerUpdate = !ModelHelper.isOriginalTraceShown(config);

            TLCModelLaunchDataProvider provider = null;
            if (isTraceExplorerUpdate)
            {
                provider = TLCOutputSourceRegistry.getTraceExploreSourceRegistry().getProvider(config);
            } else
            {
                provider = TLCOutputSourceRegistry.getModelCheckSourceRegistry().getProvider(config);
            }

            if (provider == null)
            {
                return;
            }
            TLCErrorView errorView;
            if (provider.getErrors().size() > 0 && openErrorView == true)
            {
           		errorView = (TLCErrorView) UIHelper.openView(TLCErrorView.ID);
            } else
            {
                errorView = (TLCErrorView) UIHelper.findView(TLCErrorView.ID);
            }
            if (errorView != null)
            {
                /*
                 * We need a handle on the actual underlying configuration file handle
                 * in order to retrieve the expressions that should be put in the trace
                 * explorer table. Working copies of the configuration file may not have
                 * all of the expressions that should appear. The filling of the trace
                 * explorer table occurs in the fill() method.
                 */
                if (config.isWorkingCopy())
                {
                    errorView.configFileHandle = ((ILaunchConfigurationWorkingCopy) config).getOriginal();
                } else
                {
                    errorView.configFileHandle = config;
                }

                // fill the name and the errors
                errorView.fill(ModelHelper.getModelName(provider.getConfig().getFile()), provider.getErrors());

                if (provider.getErrors().size() == 0)
                {
                    errorView.hide();
                }
            }
        } catch (CoreException e)
        {
            TLCUIActivator.getDefault().logError("Error determining if trace explorer expressions should be shown", e);
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
    static class StateContentProvider implements ITreeContentProvider
    // 
    // evtl. for path-based addressing in the tree
    // , ITreePathContentProvider
    {

        public Object[] getChildren(Object parentElement)
        {
            if (parentElement instanceof List)
            {
                return (TLCState[]) ((List) parentElement).toArray(new TLCState[((List) parentElement).size()]);
            } else if (parentElement instanceof TLCState)
            {
                TLCState state = (TLCState) parentElement;
                if (!state.isStuttering() && !state.isBackToState())
                {
                    return state.getVariables();
                }
            } else if (parentElement instanceof TLCVariable)
            {
                TLCVariable variable = (TLCVariable) parentElement;
                TLCVariableValue value = variable.getValue();
                if (value instanceof TLCSetVariableValue)
                {
                    return ((TLCSetVariableValue) value).getElements();
                } else if (value instanceof TLCSequenceVariableValue)
                {
                    return ((TLCSequenceVariableValue) value).getElements();
                } else if (value instanceof TLCFunctionVariableValue)
                {
                    return ((TLCFunctionVariableValue) value).getFcnElements();
                } else if (value instanceof TLCRecordVariableValue)
                {
                    return ((TLCRecordVariableValue) value).getPairs();
                }
                return null;
            } else if (parentElement instanceof TLCVariableValue)
            {
                TLCVariableValue value = (TLCVariableValue) parentElement;
                if (value instanceof TLCSetVariableValue)
                {
                    return ((TLCSetVariableValue) value).getElements();
                } else if (value instanceof TLCSequenceVariableValue)
                {
                    return ((TLCSequenceVariableValue) value).getElements();
                } else if (value instanceof TLCFunctionVariableValue)
                {
                    return ((TLCFunctionVariableValue) value).getFcnElements();
                } else if (value instanceof TLCRecordVariableValue)
                {
                    return ((TLCRecordVariableValue) value).getPairs();
                } else if (value instanceof TLCNamedVariableValue)
                {
                    return getChildren(((TLCNamedVariableValue) value).getValue());
                } else if (value instanceof TLCFcnElementVariableValue)
                {
                    return getChildren(((TLCFcnElementVariableValue) value).getValue());
                }
                return null;
            }
            return null;
        }

        public Object getParent(Object element)
        {
            return null;
        }

        public boolean hasChildren(Object element)
        {
            if (element instanceof List)
                return true;

            return (getChildren(element) != null);
        }

        public Object[] getElements(Object inputElement)
        {
            return getChildren(inputElement);
        }

        public void dispose()
        {
        }

        public void inputChanged(Viewer viewer, Object oldInput, Object newInput)
        {
        }
    }

    static class StateFilter extends ViewerFilter
    {

        public boolean select(Viewer viewer, Object parentElement, Object element)
        {
            return true;
        }

    }

    static class StateViewerSorter extends ViewerSorter {
    	
    	private static final String STATESORTORDER = "STATESORTORDER";

        /**
         * Sort order in which states are sorted in the variable viewer
         */
		private boolean stateSortDirection;

		private final IDialogSettings dialogSettings;

		public StateViewerSorter() {
			dialogSettings = Activator.getDefault().getDialogSettings();
			stateSortDirection = dialogSettings.getBoolean(STATESORTORDER);
		}
		
        public void reverseStateSortDirection() {
        	stateSortDirection = !stateSortDirection;
        	dialogSettings.put(STATESORTORDER, stateSortDirection);
        }
    	
		public int compare(final Viewer viewer, final Object e1, final Object e2) {
			// The error trace has to be sorted on the number of the state. An
			// unordered state sequence is rather incomprehensible. The default
			// is ordering the state trace first to last for educational reasons.
			// Advanced users are free to click the table column headers to permanently
			// change the order.
			if (e1 instanceof TLCState && e2 instanceof TLCState) {
				final TLCState s1 = (TLCState) e1;
				final TLCState s2 = (TLCState) e2;
				if(!stateSortDirection) { // negated because the default coming from DialogSettings is false
					return Integer.valueOf(s1.getStateNumber()).compareTo(s2.getStateNumber());
				} else {
					return Integer.valueOf(s2.getStateNumber()).compareTo(s1.getStateNumber());
				}
			}
			// Sort just on the label provided by the label provider
			return super.compare(viewer, e1, e2);
		}
    }
    
    /**
     * Label provider for the tree table. Modified on 30 Aug 2009 by LL to
     * implement ITableColorProvider instead of IColorProvider. This allows
     * coloring of individual columns, not just of entire rows.
     */
    static class StateLabelProvider extends LabelProvider implements ITableLabelProvider, ITableColorProvider,
            ITableFontProvider // IColorProvider
    {
        public static final int NAME = 0;
        public static final int VALUE = 1;

        public static final int[] COLUMN_WIDTH = { 200, 200 };
        public static final String[] COLUMN_TEXTS = { "Name", "Value" };

        private Image stateImage;
        private Image varImage;
        private Image recordImage;
        private Image setImage;

        public StateLabelProvider()
        {
            stateImage = TLCUIActivator.getImageDescriptor("/icons/full/default_co.gif").createImage();
            varImage = TLCUIActivator.getImageDescriptor("/icons/full/private_co.gif").createImage();
            recordImage = TLCUIActivator.getImageDescriptor("/icons/full/brkpi_obj.gif").createImage();
            // setImage = TLCUIActivator.getImageDescriptor("/icons/full/over_co.gif").createImage();
            setImage = TLCUIActivator.getImageDescriptor("/icons/full/compare_method.gif").createImage();
        }

        public Image getColumnImage(Object element, int columnIndex)
        {
            if (columnIndex == NAME)
            {
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

        public String getColumnText(Object element, int columnIndex)
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
                    return "State (num = " + state.getStateNumber() + ")";
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

        /**
         * The following method sets the background color of a row or column of
         * the table. It highlights the entire row for an added or deleted item.
         * For a changed value, only the value is highlighted.
         */
        public Color getBackground(Object element, int column)
        {
            if (changedRows.contains(element))
            {
                if (column == VALUE)
                {
                    return TLCUIActivator.getDefault().getChangedColor();
                }
            } else if (addedRows.contains(element))
            {
                return TLCUIActivator.getDefault().getAddedColor();
            } else if (deletedRows.contains(element))
            {
                return TLCUIActivator.getDefault().getDeletedColor();
            }
            return null;
        }

        /*
         * Here are the three HashSet objects that contain the objects
         * representing rows in the table displaying the trace that should be
         * highlighted. They have the following meanings:
         * 
         * changedRows: Rows indicating values that have changed from the last
         * state. Subobjects of the value column of such a row could also be
         * highlighted.
         * 
         * addedRows: Rows that have been added to a value since the last state.
         * 
         * deletedRows: Rows that are deleted in the following state.
         * 
         * The same row can appear in both the deletedRows set and the
         * changedRows or addedRows set. In that case, it should be displayed as
         * a changed or added row--since we can't do multicolored backgrounds to
         * show that it is both.
         */
        protected HashSet<Object> changedRows = new HashSet<Object>();
        protected HashSet<TLCVariableValue> addedRows = new HashSet<TLCVariableValue>();
        protected HashSet<TLCVariableValue> deletedRows = new HashSet<TLCVariableValue>();

        public Color getForeground(Object element, int i)
        {
            return null;
        }

        public Image getImage(Object element)
        {
            return getColumnImage(element, 0);
        }

        public String getText(Object element)
        {
            return getColumnText(element, 0);
        }

        public void dispose()
        {
            /*
             * Remove images
             */
            stateImage.dispose();
            varImage.dispose();
            recordImage.dispose();
            setImage.dispose();
            super.dispose();
        }

        public Font getFont(Object element, int columnIndex)
        {
            if (element instanceof TLCVariable)
            {
                TLCVariable variable = (TLCVariable) element;
                if (variable.isTraceExplorerVar())
                {
                    return JFaceResources.getFontRegistry().getBold("");
                }
            }
            return null;
        }

    }

    /*
     * Sets the HashSet objects of StateLabelProvider object that stores the
     * sets of objects to be highlighted to show state changes in the states
     * contained in the parameter stateList.
     */
    private void setDiffInfo(List<TLCState> stateList)
    {
        if (stateList.size() < 2)
        {
            return;
        }

        /*
         * Set states to the array of TLCState objects in stateList, and set
         * changedRows, addedRows, and deletedRows to the HashSet into which all
         * the appropriate row objects are put, and initialize each HashSet to
         * empty.
         */
        TLCState[] states = new TLCState[stateList.size()];
        for (int i = 0; i < states.length; i++)
        {
            states[i] = stateList.get(i);
        }
        StateLabelProvider labelProvider = (StateLabelProvider) variableViewer.getLabelProvider();
        HashSet<Object> changedRows = labelProvider.changedRows;
        HashSet<TLCVariableValue> addedRows = labelProvider.addedRows;
        HashSet<TLCVariableValue> deletedRows = labelProvider.deletedRows;
        changedRows.clear();
        addedRows.clear();
        deletedRows.clear();

        TLCState firstState = states[0];
        TLCVariable[] firstVariables = firstState.getVariables();

        for (int i = 1; i < states.length; i++)
        {
            TLCState secondState = states[i];
            if (secondState.isStuttering() || secondState.isBackToState())
            {
                // there are no variables in second state
                // because it is a stuttering or a back to state
                // step
                break;
            }
            TLCVariable[] secondVariables = secondState.getVariables();
            for (int j = 0; j < firstVariables.length; j++)
            {
                TLCVariableValue firstValue = firstVariables[j].getValue();
                TLCVariableValue secondValue = secondVariables[j].getValue();
                if (!firstValue.toSimpleString().equals(secondValue.toSimpleString()))
                {
                    changedRows.add(secondVariables[j]);
                    setInnerDiffInfo(firstValue, secondValue, changedRows, addedRows, deletedRows);
                }
            }

            firstState = secondState;
            firstVariables = secondVariables;
        }

    }

    /**
     * The recursive method called by setDiffInfo that adds the subobjects of
     * the variable value objects to the HashSets that indicate which rows of
     * the hierarchical trace table should be highlighted to show the parts of
     * the state that have changed.
     * 
     * It is called with the objects in the Value columns of corresponding
     * values that have changed. It adds rows of these two objects' table
     * representations to the appropriate HashSets to indicate that those rows
     * should be appropriately highlighted.
     */
    private void setInnerDiffInfo(TLCVariableValue first, TLCVariableValue second, HashSet<Object> changed, HashSet<TLCVariableValue> added,
            HashSet<TLCVariableValue> deleted)
    {
        if (first instanceof TLCSimpleVariableValue)
        {
            return;
        } else if (first instanceof TLCSetVariableValue)
        { /*
           * SETS For two
           * sets, the only
           * meaningful
           * changes are
           * additions and
           * deletions.
           */

            if (!(second instanceof TLCSetVariableValue))
            {
                return;
            }
            TLCVariableValue[] firstElts = ((TLCSetVariableValue) first).getElements();
            TLCVariableValue[] secondElts = ((TLCSetVariableValue) second).getElements();

            for (int i = 0; i < firstElts.length; i++)
            {
                boolean notfound = true;
                int j = 0;
                while (notfound && j < secondElts.length)
                {
                    if (firstElts[i].toSimpleString().equals(secondElts[j].toSimpleString()))
                    {
                        notfound = false;
                    }
                    j++;
                }
                if (notfound)
                {
                    deleted.add(firstElts[i]);
                }
            }

            for (int i = 0; i < secondElts.length; i++)
            {
                boolean notfound = true;
                int j = 0;
                while (notfound && j < firstElts.length)
                {
                    if (firstElts[j].toSimpleString().equals(secondElts[i].toSimpleString()))
                    {
                        notfound = false;
                    }
                    j++;
                }
                if (notfound)
                {
                    added.add(secondElts[i]);
                }
            }
        } else if (first instanceof TLCRecordVariableValue)
        {
            /*
             * RECORDS We mark a record element as added or deleted if its label
             * does not appear in one of the elements of the other record. We
             * mark the element as changed, and call setInnerDiffInfo on the
             * elements' values if elements with same label but different values
             * appear in the two records.
             */
            if (!(second instanceof TLCRecordVariableValue))
            {
                return;
            }
            TLCVariableValue[] firstElts = ((TLCRecordVariableValue) first).getPairs();
            TLCVariableValue[] secondElts = ((TLCRecordVariableValue) second).getPairs();

            String[] firstLHStrings = new String[firstElts.length];
            for (int i = 0; i < firstElts.length; i++)
            {
                firstLHStrings[i] = ((TLCNamedVariableValue) firstElts[i]).getName();
            }
            String[] secondLHStrings = new String[secondElts.length];
            for (int i = 0; i < secondElts.length; i++)
            {
                secondLHStrings[i] = ((TLCNamedVariableValue) secondElts[i]).getName();
            }

            setElementArrayDiffInfo(firstElts, firstLHStrings, secondElts, secondLHStrings, changed, added, deleted);
        } else if (first instanceof TLCFunctionVariableValue)
        {
            /*
             * FUNCTIONS We mark a record element as added or deleted if its
             * label does not appear in one of the elements of the other record.
             * We mark the element as changed, and call setInnerDiffInfo on the
             * elements' values if elements with same label but different values
             * appear in the two records.
             */
            if (!(second instanceof TLCFunctionVariableValue))
            {
                return;
            }

            setFcnElementArrayDiffInfo(((TLCFunctionVariableValue) first).getFcnElements(),
                    ((TLCFunctionVariableValue) second).getFcnElements(), changed, added, deleted);

        }

        else if (first instanceof TLCSequenceVariableValue)
        {
            /*
             * SEQUENCES In general, it's not clear how differences between two
             * sequences should be highlighted. We adopt the following
             * preliminary approach: If one sequence is a proper initial prefix
             * or suffix of the other, then the difference is interpreted as
             * adding or deleting the appropriate sequence elements. Otherwise,
             * the sequences are treated as functions.
             * 
             * Note: If one sequence is both an initial prefix and a suffix of
             * the other then we give preference to interpreting the operation
             * as adding to the end or removing from the front.
             */
            if (!(second instanceof TLCSequenceVariableValue))
            {
                return;
            }
            TLCFcnElementVariableValue[] firstElts = ((TLCSequenceVariableValue) first).getElements();
            TLCFcnElementVariableValue[] secondElts = ((TLCSequenceVariableValue) second).getElements();
            if (firstElts.length == secondElts.length)
            {
                setFcnElementArrayDiffInfo(firstElts, secondElts, changed, added, deleted);
                return;
            }

            TLCFcnElementVariableValue[] shorter = firstElts;
            TLCFcnElementVariableValue[] longer = secondElts;
            boolean firstShorter = true;
            if (firstElts.length > secondElts.length)
            {
                longer = firstElts;
                shorter = secondElts;
                firstShorter = false;
            }
            boolean isPrefix = true;
            for (int i = 0; i < shorter.length; i++)
            {
                if (!((TLCVariableValue) shorter[i].getValue()).toSimpleString().equals(
                        ((TLCVariableValue) longer[i].getValue()).toSimpleString()))
                {
                    isPrefix = false;
                    break;
                }
            }
            boolean isSuffix = true;
            for (int i = 0; i < shorter.length; i++)
            {
                if (!((TLCVariableValue) shorter[i].getValue()).toSimpleString().equals(
                        ((TLCVariableValue) longer[i + longer.length - shorter.length].getValue()).toSimpleString()))
                {

                    isSuffix = false;
                    break;
                }
            }
            /*
             * If it's both a prefix and a suffix, we interpret the change as
             * either adding to the end or deleting from the front. If it's
             * neither, we treat the sequences as functions.
             */
            if (isPrefix && isSuffix)
            {
                if (firstShorter)
                {
                    isSuffix = false;
                } else
                {
                    isPrefix = false;
                }
            } else if (!(isPrefix || isSuffix))
            {
                setFcnElementArrayDiffInfo(firstElts, secondElts, changed, added, deleted);
                return;
            }
            /*
             * There are four cases: isPrefix and firstShorter : we mark end of
             * longer (= second) as added. isPrefix and !firstShorter : we mark
             * end of longer (= first) as deleted. isSuffix and firstShorter :
             * we mark beginning of longer (=second) as added. isSuffix and
             * !firstShorter : we mark beginning of longer (=first) as deleted.
             */
            int firstEltToMark = (isPrefix) ? shorter.length : 0;
            HashSet<TLCVariableValue> howToMark = (firstShorter) ? added : deleted;

            for (int i = 0; i < longer.length - shorter.length; i++)
            {
                howToMark.add(longer[i + firstEltToMark]);
            }
            // setFcnElementArrayDiffInfo(firstElts, secondElts, changed, added,
            // deleted);
        }

        return;

    }

    /**
     * A method that sets the diff highlighting information for two arrays of
     * either TLCFcnElementVariableValue or TLCNamedVariableValue objects,
     * representing the value elements of twos values represented by
     * TLCFunctionVariableValue, TLCRecordVariableValue, or
     * TLCSequenceVariableValue objects. The parameters firstElts and secondElts
     * are the two arrays, and firstLHStrings and secondLHStrings are the
     * results of applying the toString or toSimpleString method to their first
     * elements. In plain math, this means that we are doing a diff on two
     * functions (possibly two records or two sequences) where the ...Strings
     * arrays are string representations of the domain elements of each of the
     * function elements.
     * 
     * The HashSet arguments are the sets of element objects that are to be
     * highlighted in the appropriate fashion.
     * 
     * We mark a function element as added or deleted if its left-hand value
     * does not appear in one of the elements of the other function. We mark the
     * element as changed, and call setInnerDiffInfo on the elements' values if
     * elements with the same left-hand values having different values appear in
     * the two records.
     */
    private void setElementArrayDiffInfo(TLCVariableValue[] firstElts, String[] firstLHStrings,
            TLCVariableValue[] secondElts, String[] secondLHStrings, HashSet<Object> changed, HashSet<TLCVariableValue> added, HashSet<TLCVariableValue> deleted)
    {

        for (int i = 0; i < firstElts.length; i++)
        {
            boolean notfound = true;
            int j = 0;
            while (notfound && j < secondElts.length)
            {
                if (firstLHStrings[i].equals(secondLHStrings[j]))
                {
                    notfound = false;
                    TLCVariableValue first = (TLCVariableValue) firstElts[i].getValue();
                    TLCVariableValue second = (TLCVariableValue) secondElts[j].getValue();
                    if (!first.toSimpleString().equals(second.toSimpleString()))
                    {
                        changed.add(secondElts[j]);
                        setInnerDiffInfo(first, second, changed, added, deleted);
                    }
                }
                j++;
            }
            if (notfound)
            {
                deleted.add(firstElts[i]);
            }
        }

        for (int i = 0; i < secondElts.length; i++)
        {
            boolean notfound = true;
            int j = 0;
            while (notfound && j < firstElts.length)
            {
                if (firstElts[j].toSimpleString().equals(secondElts[i].toSimpleString()))
                {
                    notfound = false;
                }
                j++;
            }
            if (notfound)
            {
                added.add(secondElts[i]);
            }
        }

    }

    /**
     * A method that sets the diff highlighting information for two arrays of
     * TLCFcnElementVariableValue objects. The parameters firstElts and
     * secondElts are the two arrays.In plain math, this means that we are doing
     * a diff on two functions (possibly two sequences). This method calls
     * setElementArrayDiffInfo to do the work.
     */
    private void setFcnElementArrayDiffInfo(TLCFcnElementVariableValue[] firstElts,
            TLCFcnElementVariableValue[] secondElts, HashSet<Object> changed, HashSet<TLCVariableValue> added, HashSet<TLCVariableValue> deleted)
    {
        String[] firstLHStrings = new String[firstElts.length];
        for (int i = 0; i < firstElts.length; i++)
        {
            firstLHStrings[i] = firstElts[i].getFrom().toSimpleString();
        }
        String[] secondLHStrings = new String[secondElts.length];
        for (int i = 0; i < secondElts.length; i++)
        {
            secondLHStrings[i] = secondElts[i].getFrom().toSimpleString();
        }
        setElementArrayDiffInfo(firstElts, firstLHStrings, secondElts, secondLHStrings, changed, added, deleted);
    }

    public List getTrace()
    {
        if (variableViewer == null)
        {
            return null;
        }
        return (List) variableViewer.getInput();
    }

    /**
     * Returns a handle on the underlying configuration file for which
     * errors are being shown by this view. Can return null.
     * 
     * @return
     */
    public ILaunchConfiguration getCurrentConfigFileHandle()
    {
        return configFileHandle;
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
    private void setTraceInput(List<TLCState> states)
    {
        variableViewer.setInput(states);
        if (!states.isEmpty())
        {
            valueViewer.setDocument(NO_VALUE_DOCUMENT());
        } else
        {
            valueViewer.setDocument(EMPTY_DOCUMENT());
        }
    }
}
