package org.lamport.tla.toolbox.tool.tlc.ui.view;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Vector;
import java.util.regex.Pattern;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITableColorProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.events.ControlAdapter;
import org.eclipse.swt.events.ControlEvent;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.ScrollBar;
import org.eclipse.swt.widgets.Scrollable;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.ui.forms.widgets.Form;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.eclipse.ui.forms.widgets.TableWrapLayout;
import org.eclipse.ui.part.ViewPart;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.launch.TraceExplorerDelegate;
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
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.TraceExplorerComposite;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.provider.FormulaContentProvider;
import org.lamport.tla.toolbox.tool.tlc.ui.util.ActionClickListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.TLCUIHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
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
    public static final String ID = "toolbox.tool.tlc.view.TLCErrorView";

    private static final String TOOLTIP = "Click on a row to see in viewer, double-click to go to action in spec.";

    /*
     * These are used for writing init and next
     * for trace exploration.
     */
    private static final String TLA_AND = "/\\ ";
    private static final String TLA_OR = "\\/ ";
    private static final String EQ = "=";
    private static final String PRIME = "'";

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

    private static final List EMPTY_LIST()
    {
        return new LinkedList();
    }

    private FormToolkit toolkit;
    private Form form;

    private SourceViewer errorViewer;
    private TreeViewer variableViewer;
    private SourceViewer valueViewer;
    private ILaunchConfiguration currentConfig;
    private TraceExplorerComposite traceExplorerComposite;

    /**
     * Clears the view
     */
    public void clear()
    {
        errorViewer.setDocument(EMPTY_DOCUMENT());
        variableViewer.setInput(EMPTY_LIST());
        traceExplorerComposite.getTableViewer().setInput(new Vector());
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
    protected void fill(String modelName, List problems)
    {

        // Fill the trace explorer expression table
        // with expressions saved in the config
        try
        {
            /*
             * FormHelper.setSerializedInput adds elements from the list that is
             * the second argument to the existing input of the table viewer
             * that is the first argument. In order to avoid adding duplicate
             * entries to the table, we must first set the trace explorer
             * table to an empty input before calling FormHelper.setSerializedInput.
             */
            traceExplorerComposite.getTableViewer().setInput(new Vector());
            FormHelper.setSerializedInput(traceExplorerComposite.getTableViewer(), currentConfig.getAttribute(
                    IModelConfigurationConstants.TRACE_EXPLORE_EXPRESSIONS, new Vector()));
        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error loading trace explorer expressions into table", e);
        }

        // if there are errors
        if (problems != null && !problems.isEmpty())
        {
            List states = null;
            StringBuffer buffer = new StringBuffer();
            // iterate over the errors
            for (int i = 0; i < problems.size(); i++)
            {
                TLCError error = (TLCError) problems.get(i);

                // append error text to the buffer
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
                states = EMPTY_LIST();
            }

            /*
             * determine if trace has changed this is important for really long
             * traces resetting the trace input locks up the toolbox for a few
             * seconds in these cases, so it is important to not reset the trace
             * if it is not necessary
             */
            List oldStates = (List) variableViewer.getInput();
            boolean isNewTrace = states != null && oldStates != null && !(states == oldStates);

            /*
             * Set the data structures that cause highlighting of changes in the
             * error trace.
             */
            if (isNewTrace)
            {
                setDiffInfo(states);
            }

            // update the error information in the TLC Error View
            IDocument document = errorViewer.getDocument();
            try
            {
                document.replace(0, document.getLength(), buffer.toString());
            } catch (BadLocationException e)
            {
                TLCUIActivator.logError("Error reporting the error " + buffer.toString(), e);
            }

            // update the trace information
            if (isNewTrace)
            {
                this.variableViewer.setInput(states);
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
        SashForm outerSashForm = new SashForm(body, SWT.VERTICAL);
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
         * table section and the inner sash form.
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

        traceExplorerComposite = new TraceExplorerComposite(belowErrorViewerComposite, "Trace Explorer",
                "Enter expressions to be evaluated at each state of the trace", toolkit, this);

        // Modified on 30 Aug 2009 as part of putting error viewer inside a
        // sash.
        // SashForm sashForm = new SashForm(body, SWT.VERTICAL); //
        SashForm sashForm = new SashForm(belowErrorViewerComposite, SWT.VERTICAL);
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

        for (int i = 0; i < StateLabelProvider.COLUMN_TEXTS.length; i++)
        {
            TreeColumn column = new TreeColumn(tree, SWT.LEFT);
            column.setText(StateLabelProvider.COLUMN_TEXTS[i]);
            column.setWidth(StateLabelProvider.COLUMN_WIDTH[i]);
            resizer.column[i] = column; // set up the resizer.
            column.setToolTipText(TOOLTIP);
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

        variableViewer.addDoubleClickListener(new ActionClickListener());

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
                    valueViewer.setDocument(new Document(selection.toString()));
                } else
                {
                    valueViewer.setDocument(EMPTY_DOCUMENT());
                }

            }
        });

        /* Horizontal scroll bar added by LL on 26 Aug 2009 */
        valueViewer = FormHelper.createFormsSourceViewer(toolkit, sashForm, SWT.V_SCROLL | SWT.H_SCROLL | SWT.MULTI
                | SWT.BORDER);
        valueViewer.setEditable(false);

        gd = new GridData(SWT.LEFT, SWT.TOP, true, false);
        valueViewer.getControl().setLayoutData(gd);

        /*
         * Following statement added by LL on 30 Aug 2009 to make the trace
         * viewer sash higher than the error viewer sash.
         */
        int[] weights = { 1, 4 };
        outerSashForm.setWeights(weights);

        // init
        clear();

        TLCUIHelper.setHelp(parent, IHelpConstants.TLC_ERROR_VIEW);
    }

    public void setFocus()
    {
        form.setFocus();
    }

    public void dispose()
    {
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
                    "The `Evaluate Constant Expression’ section’s evaluation");
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
     * 
     * @param errors
     *            a list of {@link TLCError}
     */
    public static void updateErrorView(TLCModelLaunchDataProvider provider)
    {

        if (provider == null)
        {
            return;
        }
        TLCErrorView errorView;
        if (provider.getErrors().size() > 0)
        {
            errorView = (TLCErrorView) UIHelper.openView(TLCErrorView.ID);
        } else
        {
            errorView = (TLCErrorView) UIHelper.findView(TLCErrorView.ID);
        }
        if (errorView != null)
        {

            errorView.currentConfig = provider.getConfig();

            // fill the name and the errors
            errorView.fill(ModelHelper.getModelName(provider.getConfig().getFile()), provider.getErrors());

            if (provider.getErrors().size() == 0)
            {
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

    /**
     * Label provider for the tree table. Modified on 30 Aug 2009 by LL to
     * implement ITableColorProvider instead of IColorProvider. This allows
     * coloring of individual columns, not just of entire rows.
     */
    static class StateLabelProvider extends LabelProvider implements ITableLabelProvider, ITableColorProvider // IColorProvider
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
                    return var.getName();
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
        protected HashSet changedRows = new HashSet();
        protected HashSet addedRows = new HashSet();
        protected HashSet deletedRows = new HashSet();

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

    }

    /*
     * Sets the HashSet objects of StateLabelProvider object that stores the
     * sets of objects to be highlighted to show state changes in the states
     * contained in the parameter stateList.
     */
    private void setDiffInfo(List stateList)
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
            states[i] = (TLCState) stateList.get(i);
        }
        StateLabelProvider labelProvider = (StateLabelProvider) variableViewer.getLabelProvider();
        HashSet changedRows = labelProvider.changedRows;
        HashSet addedRows = labelProvider.addedRows;
        HashSet deletedRows = labelProvider.deletedRows;
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
    private void setInnerDiffInfo(TLCVariableValue first, TLCVariableValue second, HashSet changed, HashSet added,
            HashSet deleted)
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
            HashSet howToMark = (firstShorter) ? added : deleted;

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
            TLCVariableValue[] secondElts, String[] secondLHStrings, HashSet changed, HashSet added, HashSet deleted)
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
            TLCFcnElementVariableValue[] secondElts, HashSet changed, HashSet added, HashSet deleted)
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

    private void setUpTraceExplorerSection(Composite parent, FormToolkit toolkit)
    {
        GridData gd;

        Section section = FormHelper.createSectionComposite(parent, "Trace Explorer",
                "Enter expressions to be evaluated at each state of the trace.", toolkit);

        Composite sectionArea = (Composite) section.getClient();

        sectionArea.setLayout(new GridLayout(2, false));

        // create the table to contain the expressions
        Table table = toolkit.createTable(sectionArea, SWT.MULTI | SWT.CHECK | SWT.V_SCROLL | SWT.H_SCROLL
                | SWT.FULL_SELECTION);
        table.setLinesVisible(false);
        table.setHeaderVisible(false);

        gd = new GridData(GridData.FILL_BOTH);
        gd.grabExcessHorizontalSpace = true;
        gd.grabExcessVerticalSpace = true;
        // span for the buttons
        gd.verticalSpan = 3;
        table.setLayoutData(gd);
    }

    private class ExploreAction extends Action
    {

        ExploreAction()
        {
            super("Explore", TLCUIActivator.imageDescriptorFromPlugin(TLCUIActivator.PLUGIN_ID,
                    "icons/full/lrun_obj.gif"));
            this.setDescription("Explores the trace.");
            this.setToolTipText("Explores the trace.");
        }

        public void run()
        {
            // // get the launch manager
            // ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
            //
            // // get the launch type (model check)
            // ILaunchConfigurationType launchConfigurationType = launchManager
            // .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_CONFIGURATION_TYPE);
            //
            // // create new launch instance
            // try
            // {
            // String modelName = "traceTest";
            // String configName = ToolboxHandle.getCurrentSpec().getName() + "___" + modelName;
            // ILaunchConfiguration[] configs = launchManager.getLaunchConfigurations(launchConfigurationType);
            // ILaunchConfiguration config = null;
            // for (int i = 0; i < configs.length; i++)
            // {
            // if (configs[i].getName().equals(configName))
            // {
            // config = configs[i];
            // }
            // }
            // if (config == null)
            // {
            // // retrieve the model folder
            // IProject project = ToolboxHandle.getCurrentSpec().getProject();
            // IFolder modelFolder = project.getFolder(modelName);
            // if (!modelFolder.exists())
            // {
            // return;
            // }
            // IFolder traceFolder = modelFolder.getFolder(modelName);
            // if (!traceFolder.exists())
            // {
            // traceFolder.create(IResource.DERIVED | IResource.FORCE, true, new NullProgressMonitor());
            // }
            // ILaunchConfigurationWorkingCopy launchCopy = launchConfigurationType.newInstance(project,
            // configName);
            // launchCopy.setAttribute(IConfigurationConstants.MODEL_NAME, modelName);
            // launchCopy
            // .setAttribute(IConfigurationConstants.SPEC_NAME, ToolboxHandle.getCurrentSpec().getName());
            // config = launchCopy.doSave();
            // }
            // config.launch(TLCModelLaunchDelegate.MODE_MODELCHECK, new NullProgressMonitor(), true);
            // } catch (CoreException e)
            // {
            // // TODO Auto-generated catch block
            // e.printStackTrace();
            // }
            explore();

        }

        public boolean isEnabled()
        {
            return true;
        }

    }

    private void explore()
    {
        // // ILaunchConfiguration config = ModelHelper.getTraceExploreConfigByName(modelName);
        // ILaunchConfiguration modelConfig = ModelHelper.getModelByName(modelName);
        // try
        // {
        // ILaunchConfigurationWorkingCopy configCopy = modelConfig.getWorkingCopy();
        // configCopy.setAttribute(IModelConfigurationConstants.TRACE_EXPLORE_INIT, getInitFromTrace());
        // configCopy.setAttribute(IModelConfigurationConstants.TRACE_EXPLORE_NEXT, getNextFromTrace());
        //
        // // configCopy.doSave().launch(TLCModelLaunchDelegate.MODE_TRACE_EXPLORE, new NullProgressMonitor(), true);
        // } catch (CoreException e)
        // {
        // // TODO Auto-generated catch block
        // e.printStackTrace();
        // }

    }

    private String getInitFromTrace()
    {
        List trace = (List) variableViewer.getInput();
        Object firstElement = (TLCState) trace.get(0);
        StringBuffer initPredicate = new StringBuffer();
        if (firstElement instanceof TLCState)
        {
            TLCState initState = (TLCState) firstElement;
            if (initState.getLabel().contains("<Initial predicate>"))
            {
                TLCVariable[] variables = initState.getVariables();
                for (int i = 0; i < variables.length; i++)
                {
                    TLCVariable var = variables[i];
                    initPredicate.append(TLA_AND).append(var.getName()).append(EQ).append(
                            var.getValue().toSimpleString()).append("\n");
                }
            } else
            {
                TLCUIActivator.logDebug("The first element of the trace is not the initial predicate. This is a bug.");
            }
        }
        return initPredicate.toString();
    }

    private String getNextFromTrace()
    {
        StringBuffer nextPredicate = new StringBuffer();

        List trace = (List) variableViewer.getInput();
        Iterator it = trace.iterator();
        TLCState currentState = null;
        TLCState nextState = null;
        if (it.hasNext())
        {
            Object first = it.next();
            Assert
                    .isTrue(first instanceof TLCState,
                            "The first element of the trace is not a TLCState. This is a bug.");
            currentState = (TLCState) first;
        } else
        {
            return "";
        }
        while (it.hasNext())
        {
            Object next = it.next();
            Assert.isTrue(next instanceof TLCState, "An element of the trace is not a TLCState. It is an instance of "
                    + next.getClass().getCanonicalName() + ". This is a bug.");
            nextState = (TLCState) next;
            // must take into account stuttering states
            // and back to state states
            // need to test to see if this behaves properly
            if (nextState.isBackToState() || nextState.isStuttering())
            {
                break;
            }
            nextPredicate.append(TLA_OR);
            TLCVariable[] currentStateVariables = currentState.getVariables();
            TLCVariable[] nextStateVariables = nextState.getVariables();
            Assert.isTrue(currentStateVariables.length == nextStateVariables.length,
                    "The number of variables in one state is not the same as in another state of the trace.");

            for (int i = 0; i < currentStateVariables.length; i++)
            {
                TLCVariable var = currentStateVariables[i];
                nextPredicate.append(TLA_AND).append(var.getName()).append(EQ).append(var.getValue().toSimpleString())
                        .append("\n");
            }

            for (int i = 0; i < nextStateVariables.length; i++)
            {
                TLCVariable var = nextStateVariables[i];
                nextPredicate.append(TLA_AND).append(var.getName()).append(PRIME).append(EQ).append(
                        var.getValue().toSimpleString()).append("\n");
            }

            currentState = nextState;
        }

        return nextPredicate.toString();
    }

    public ILaunchConfiguration getCurrentConfig()
    {
        return currentConfig;
    }
}
