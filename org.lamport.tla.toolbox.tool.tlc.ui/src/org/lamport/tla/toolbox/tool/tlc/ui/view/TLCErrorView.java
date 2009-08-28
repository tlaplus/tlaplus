package org.lamport.tla.toolbox.tool.tlc.ui.view;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.IColorProvider;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.ui.forms.widgets.Form;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
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
 * Error representation
 * @author Simon Zambrovski
 * @version $Id$
 * This is the view of the error description.  
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
     * Fill data
     */
    protected void fill(String modelName, List problems)
    {
        if (problems != null && !problems.isEmpty())
        {
            List states = null;
            StringBuffer buffer = new StringBuffer();

            for (int i = 0; i < problems.size(); i++)
            {
                TLCError error = (TLCError) problems.get(i);
                appendError(buffer, error);
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
             * lamport:test this is test code added by LL on 27 Aug 2009 Add
             * code here to set trace diff highliter information
             */
            setDiffInfo(states);

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
            this.variableViewer.setInput(states);
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
        int sectionFlags = Section.DESCRIPTION | Section.TITLE_BAR | Section.EXPANDED | Section.TWISTIE;
        toolkit = new FormToolkit(parent.getDisplay());
        form = toolkit.createForm(parent);
        form.setText("");
        toolkit.decorateFormHeading(form);

        GridLayout layout;
        GridData gd;
        Composite body = form.getBody();
        layout = new GridLayout(1, false);
        body.setLayout(layout);

        // error section
        Section section = FormHelper.createSectionComposite(body, "Error", "", toolkit, sectionFlags, null);
        gd = new GridData(SWT.FILL, SWT.FILL, true, false);
        section.setLayoutData(gd);
        Composite clientArea = (Composite) section.getClient();
        layout = new GridLayout();
        clientArea.setLayout(layout);

        errorViewer = FormHelper.createFormsOutputViewer(toolkit, clientArea, SWT.V_SCROLL | SWT.MULTI);
        gd = new GridData(SWT.FILL, SWT.FILL, true, false);
        gd.heightHint = 100;
        errorViewer.getControl().setLayoutData(gd);

        SashForm sashForm = new SashForm(body, SWT.VERTICAL);
        toolkit.adapt(sashForm);
        gd = new GridData(SWT.FILL, SWT.FILL, true, true);
        sashForm.setLayoutData(gd);

        Tree tree = toolkit.createTree(sashForm, SWT.V_SCROLL | SWT.BORDER | SWT.FULL_SELECTION | SWT.SINGLE);
        tree.setHeaderVisible(true);
        tree.setLinesVisible(true);

        gd = new GridData(SWT.LEFT, SWT.TOP, true, false);
        gd.minimumHeight = 300;
        // gd.minimumWidth = 300;
        tree.setLayoutData(gd);

        for (int i = 0; i < StateLabelProvider.COLUMN_TEXTS.length; i++)
        {
            TreeColumn column = new TreeColumn(tree, SWT.LEFT);
            column.setText(StateLabelProvider.COLUMN_TEXTS[i]);
            column.setWidth(StateLabelProvider.COLUMN_WIDTH[i]);
        }

        variableViewer = new TreeViewer(tree);
        variableViewer.setContentProvider(new StateContentProvider());
        variableViewer.setFilters(new ViewerFilter[] { new StateFilter() });
        variableViewer.setLabelProvider(new StateLabelProvider());
        variableViewer.addSelectionChangedListener(new ISelectionChangedListener() {

            public void selectionChanged(SelectionChangedEvent event)
            {
                if (!((IStructuredSelection) event.getSelection()).isEmpty())
                {
                    // Set selection to the selected element (or the first if there are multiple
                    // selections), and show its string representation in the value viewer
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
     * @param buffer
     * @param error
     */
    private static void appendError(StringBuffer buffer, TLCError error)
    {
        buffer.append(error.getMessage()).append("\n");
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
                if (!state.isStuttering())
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
     * Label provider for the tree table
     */
    static class StateLabelProvider extends LabelProvider implements ITableLabelProvider, IColorProvider
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
                    return var.getValue().toString();
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
                    return namedValue.getValue().toString();
                default:
                    break;
                }
            } else if (element instanceof TLCFcnElementVariableValue)
            {
                TLCFcnElementVariableValue fcnElementValue = (TLCFcnElementVariableValue) element;
                switch (columnIndex) {
                case NAME:
                    return fcnElementValue.getFrom().toString();
                case VALUE:
                    return fcnElementValue.getValue().toString();
                default:
                    break;
                }
            }
            return null;
        }

        /*
         * begin lamport:test
         */

        /*
         * The following method sets the background color OF THE ENTIRE ROW of
         * the table. It can be used for highlighting the entire row to show a
         * changed value. I don't know how to highlight just one column entry of
         * the row. Apparently, all that can be done is to change the text
         * itself.
         */
        public Color getBackground(Object element)
        {
            if (changedRows.contains(element))
            {
                return changedColor;
            } else if (addedRows.contains(element))
            {
                return addedColor;
            } else if (deletedRows.contains(element))
            {
                return deletedColor;
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

        /*
         * The colors used for trace row highlighting. These should be in some
         * central location containing all colors and fonts to make it easy to
         * make them changeable by preferences.
         */
        private Color changedColor = new Color(null, 255, 200, 200);
        private Color addedColor = new Color(null, 255, 255, 200);
        private Color deletedColor = new Color(null, 240, 240, 255);

        /*
         * end lamport:test
         */

        public Color getForeground(Object element)
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

            /*
             * Remove the colors
             */
            addedColor.dispose();
            changedColor.dispose();
            deletedColor.dispose();

            super.dispose();
        }

    }

    /*
     * lamport:test From here to the end of the file is a test version of
     * objects and methods used for highlighting changes in the error trace.
     */

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

        /*
         * As a test, put the changed variable values in changedObjects.
         */
        TLCState firstState = states[0];
        TLCVariable[] firstVariables = firstState.getVariables();

        for (int i = 1; i < states.length; i++)
        {
            TLCState secondState = states[i];
            TLCVariable[] secondVariables = secondState.getVariables();
            for (int j = 0; j < firstVariables.length; j++)
            {
                TLCVariableValue firstValue = firstVariables[j].getValue();
                TLCVariableValue secondValue = secondVariables[j].getValue();
                if (!firstValue.toString().equals(secondValue.toString()))
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
        }
        else if (first instanceof TLCFunctionVariableValue)
        {
            /*
             * RECORDS We mark a record element as added or deleted if its label
             * does not appear in one of the elements of the other record. We
             * mark the element as changed, and call setInnerDiffInfo on the
             * elements' values if elements with same label but different values
             * appear in the two records.
             */
            if (!(second instanceof TLCFunctionVariableValue))
            {
                return;
            }
            TLCFcnElementVariableValue[] firstElts = ((TLCFunctionVariableValue) first).getFcnElements();
            TLCFcnElementVariableValue[] secondElts = ((TLCFunctionVariableValue) second).getFcnElements();
            setFcnElementArrayDiffInfo(firstElts,  secondElts,  changed, added, deleted);
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
            secondLHStrings[i] =  secondElts[i].getFrom().toSimpleString();
        }
        setElementArrayDiffInfo(firstElts, firstLHStrings, secondElts, secondLHStrings, changed, added, deleted);
    }
}
