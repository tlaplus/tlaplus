package org.lamport.tla.toolbox.tool.tlc.ui.view;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.SourceViewer;
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
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.ScrollBar;
import org.eclipse.swt.widgets.Scrollable;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.ui.forms.widgets.Form;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.part.ViewPart;
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
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Error representation view containing the error description and the trace explorer.
 * This is the view of the error description.  
 * @author Simon Zambrovski
 * @version $Id$
 */

public class TLCErrorView extends ViewPart
{
    public static final String ID = "toolbox.tool.tlc.view.TLCErrorView";

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

    /**
     * Clears the view
     */
    public void clear()
    {
        errorViewer.setDocument(EMPTY_DOCUMENT());
        variableViewer.setInput(EMPTY_LIST());
    }

    /**
     * Fill data into the view
     * @param modelName name of the model displayed in the view title section
     * @param problems a list of {@link TLCError} objects representing the errors.
     */
    protected void fill(String modelName, List problems)
    {
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
             *  determine if trace has changed
             *  this is important for really long traces
             *  resetting the trace input locks up the
             *  toolbox for a few seconds in
             *  these cases, so it is important to not
             *  reset the trace if it is not necessary
             */
            List oldStates = (List) variableViewer.getInput();
            boolean isNewTrace = states != null && oldStates != null && !states.equals(oldStates);

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

        // Modified on 30 Aug 2009 as part of putting error viewer inside a
        // sash.
        // SashForm sashForm = new SashForm(body, SWT.VERTICAL); //
        SashForm sashForm = new SashForm(outerSashForm, SWT.VERTICAL);
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

        for (int i = 0; i < StateLabelProvider.COLUMN_TEXTS.length; i++)
        {
            TreeColumn column = new TreeColumn(tree, SWT.LEFT);
            column.setText(StateLabelProvider.COLUMN_TEXTS[i]);
            column.setWidth(StateLabelProvider.COLUMN_WIDTH[i]);
            resizer.column[i] = column; // set up the resizer.
        }

        sashForm.addControlListener(resizer);
        // I need to add a listener for size changes to column[0] to
        // detect when the user has tried to resize the individual columns.
        // The following might work, if I can figure out the real event type
        // to use.
        int eventType = SWT.Resize; // (2^25) - 1 ; // 1023; // what should this
        // be?
        resizer.column[0].addListener(eventType, resizer);

        ScrollBar hBar = tree.getHorizontalBar();

        hBar.addListener(SWT.Show, resizer);

        variableViewer = new TreeViewer(tree);
        variableViewer.setContentProvider(new StateContentProvider());
        variableViewer.setFilters(new ViewerFilter[] { new StateFilter() });
        variableViewer.setLabelProvider(new StateLabelProvider());
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

        UIHelper.setHelp(parent, "TLCErrorView");
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
     * Appends the error description to the buffer
     * @param buffer string buffer to append the error description to
     * @param error error object
     */
    private static void appendError(StringBuffer buffer, TLCError error)
    {
        String message = error.getMessage();
        if (message != null && !message.equals(""))
        {
            buffer.append(message).append("\n");
        }
        if (error.getCause() != null)
        {
            appendError(buffer, error.getCause());
        }
    }

    /**
     * Display the errors in the view, or hides the view if no errors
     * @param errors a list of {@link TLCError}
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
     * when the sashForm containing the tree is resized. handleEvent - called
     * when column[0] is resized. The controlResized command can change the size
     * of column[0], which triggers the calling of the handleEvent.
     * Experimentation indicates that this call of handleEvent occurs in the
     * middle of executing the call of controlResized. The boolean flag
     * inControlResized is used to tell the handleEvent method whether it was
     * called this way or by the user resizing the colulmn.
     * 
     * Note: I am assuming that the call of handleEvent that happens when
     * controlResized is resizing column[0] happens during the execution of
     * column[0].setWidth, and no funny races are possible.
     * 
     * Note that all the code here assumes that there are two columns. It needs
     * to be modified if the number of columns is changed.
     * 
     * The code in the controlResized method that does the actual resizing of
     * the columns was copied from Snippet77 from
     * http://www.eclipse.org/swt/snippets/ (see under Tables.../resize columns
     * as table resizes).
     */
    static class TraceDisplayResizer extends ControlAdapter implements Listener
    {

        // See comments above for meaning of the following flag.
        boolean inControlResized = false;

        // firstColPercentageWidth is the percentage of the total width of the
        // display occupied by the first column times 1000. The factor of 10000
        // is
        // needed when computing ratios to prevent roundoff error from scewing
        // things
        // up too quickly. However, I haven't done the math to see if this will
        // cause overflow (which in Java means turning a big number into a small
        // one)
        // with large screens.

        int firstColPercentageWidth = 50000;
        Scrollable comp; // The component containing the trace display.
        TreeColumn[] column = new TreeColumn[StateLabelProvider.COLUMN_TEXTS.length];
        Tree tree;
        // oldWidth1 is the width of column 1 the last time this
        // the tree was resized. The idea is that if the user has changed the
        // relative dimensions, we want to keep column 0 about the size to which
        // it was just set. It is initialized to -1, in which case the current
        // width of column 1 is used instead.
        int oldWidth1 = -1;
        /*
         * I want to have the tree columns fill the tree's allotted horizontal
         * space. If I use the formula from Snippet77, the -tree.computeTrim...
         * term makes the tree too narrow. If I exclude that term, the formula
         * makes the tree a little too wide, producing a horizontal scrollbar.
         * So, I subtract a "fudge factor" that I experimentally determined to
         * be just big enough to avoid the scrollbar. However, it seems unlikely
         * that this magic number will be big enough on all platforms. So, it is
         * dynamically increased until it is big enough. However, that increase
         * happens only when the tree is redisplayed. So if this particular
         * value is too small, the error trace window will have a scrollbar the
         * first time it is displayed. When it gets redisplayed, the scrollbar
         * will disappear.
         */
        int fudgeFactor = 4;

        public void controlResized(ControlEvent e)
        {

            inControlResized = true;

            Rectangle area = comp.getClientArea();
            // Point size = tree.computeSize(SWT.DEFAULT, SWT.DEFAULT);
            Point oldSize = tree.getSize();
            ScrollBar hBar = tree.getHorizontalBar();
            int width = getWidth();
            // System.out.println("vbar width: " +
            // tree.getVerticalBar().getSize().x);
            // System.out.println("width: " + width);
            // System.out.println("area.idth: " + area.width);

            // I would like to preserve relative size changes of the columns
            // made by the user, but I can't seem to figure out how to do that
            // reasonably. The following code does a half-decent job. But
            // it needs to be thought out more carefully.
            do
            {

                // The following stuff became irrelevant when we added the
                // handleEvent
                // method that sets firstColPercentageWidth.
                // if (width > 0) {
                // int old1 = (oldWidth1 > 0) ? oldWidth1 : column[1]
                // .getWidth();
                // int newWidth = (100000 * column[0].getWidth())
                // / (column[0].getWidth() + old1 /*
                // * column[1].getWidth(
                // * )
                // */);
                // // We don't let firstColPercentageWidth change to make
                // // column 0 too small or too large. We also don't change it
                // // if the change is small. This prevents roundoff error from
                // // making the column size drift when it hasn't really been
                // // changed.
                // // All this kludgery would disappear if we could modify
                // // firstColPercentageWidth only when the user resizes the
                // // individual columns. But I can't figure out how to find
                // // out when that happens.
                // if (newWidth > 10000
                // && newWidth < 90000
                // && (newWidth - firstColPercentageWidth > 5000 || newWidth
                // - firstColPercentageWidth < -5000)) {
                // firstColPercentageWidth = newWidth;
                // }
                // }
                if (oldSize.x > area.width)
                {
                    // table is getting smaller so make the columns
                    // smaller first and then resize the table to
                    // match the client area width
                    column[0].setWidth((firstColPercentageWidth * width) / 100000);
                    column[1].setWidth(width - column[0].getWidth());
                    tree.setSize(area.width, area.height);
                } else
                {
                    // table is getting bigger so make the table
                    // bigger first and then make the columns wider
                    // to match the client area width
                    tree.setSize(area.width, area.height);
                    column[0].setWidth((firstColPercentageWidth * width) / 100000);
                    column[1].setWidth(width - column[0].getWidth());
                }
                if (hBar.isVisible())
                {
                    fudgeFactor++;
                    width = getWidth();
                    // System.out.println("Fudge factor = " + fudgeFactor);
                }
            } while (hBar.isVisible());

            inControlResized = false;

            oldWidth1 = column[1].getWidth();

            // System.out.println("new widths: " + column[0].getWidth() + ", "
            // + column[1].getWidth());
            // System.out.println("firstColPercentageWidth: " +
            // firstColPercentageWidth);
        }

        int count = 0;

        public void handleEvent(Event event)
        {
            if (inControlResized)
            {
                // Inside call of controlResized; do nothing.
                // System.out
                // .println("Call of handleEvent inside call of controlResized");
                return;
            }
            // We now resize the columns so that column[0] maintains the size
            // set by the user and column[1] fills the rest of the tree's
            // allotted space.
            // We also set firstColPercentageWidth to represent the percentage
            // of the
            // horizontal space occupied by the first column. However, we don't
            // let it
            // become less than 10% or greater than 90%.
            ScrollBar hBar = tree.getHorizontalBar();
            int width = getWidth();
            do
            {
                if (width == 0)
                {
                    return;
                }
                column[1].setWidth(width - column[0].getWidth());
                firstColPercentageWidth = (100000 * column[0].getWidth()) / width;
                if (hBar.isVisible())
                {
                    fudgeFactor++;
                    width = getWidth();
                    // System.out.println("Fudge factor = " + fudgeFactor);
                }
            } while (hBar.isVisible());
            if (firstColPercentageWidth < 10000)
            {
                firstColPercentageWidth = 10000;
            }
            if (firstColPercentageWidth > 90000)
            {
                firstColPercentageWidth = 90000;
            }

            // System.out.println("Event Reported" + count++ + ", "
            // + firstColPercentageWidth + ", " + width + ", "
            // + column[0].getWidth());
        }

        /*
         * The value of getWidth() should be the sum of the widths of the two
         * columns.
         */
        private int getWidth()
        {
            ScrollBar vBar = tree.getVerticalBar();
            boolean scrollBarShown = vBar.isVisible();
            Rectangle area = comp.getClientArea();
            return area.width - fudgeFactor // - tree.computeTrim(0,0,0,0).width
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
     * Label provider for the tree table.
     * Modified on 30 Aug 2009 by LL to implement ITableColorProvider instead of IColorProvider.
     * This allows coloring of individual columns, not just of entire rows.
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

        public StateLabelProvider()
        {
            stateImage = TLCUIActivator.getImageDescriptor("/icons/full/default_co.gif").createImage();
            varImage = TLCUIActivator.getImageDescriptor("/icons/full/private_co.gif").createImage();
            recordImage = TLCUIActivator.getImageDescriptor("/icons/full/brkpi_obj.gif").createImage();
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
                return null;
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
           * SETS For two sets,
           * the only meaningful
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
     * TLCFcnElementVariableValue objects.  The parameters firstElts and secondElts
     * are the two arrays.In plain math, this means that we are doing a diff on two
     * functions (possibly  two sequences).  This method calls setElementArrayDiffInfo
     * to do the work.
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
}
