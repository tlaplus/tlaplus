package org.lamport.tla.toolbox.tool.tlc.ui.view;

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
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCError;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCFcnElementVariableValue;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCFunctionVariableValue;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCNamedVariableValue;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCRecordVariableValue;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCSequenceVariableValue;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCSetVariableValue;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCSimpleVariableValue;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCState;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCVariable;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCVariableValue;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
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
    private static final IDocument EMPTY_DOCUMENT = new Document("No error information");
    private static final List EMPTY_LIST = new LinkedList();

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
        errorViewer.setDocument(EMPTY_DOCUMENT);
        variableViewer.setInput(EMPTY_LIST);
    }

    /**
     * Fill data
     */
    public void fill(List problems)
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
                states = EMPTY_LIST;
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
            this.variableViewer.setInput(states);

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
                    valueViewer.setDocument(EMPTY_DOCUMENT);
                }

            }
        });

        /* Horizontal scroll bar added by LL on 26 Aug 2009 */
        valueViewer = FormHelper.createFormsSourceViewer(toolkit, sashForm, SWT.V_SCROLL | SWT.H_SCROLL | SWT.MULTI | SWT.BORDER);
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
    public static void updateErrorView(final List errors)
    {
        UIHelper.runUIAsync(new Runnable() {

            public void run()
            {
                TLCErrorView errorView;
                if (errors.size() > 0)
                {
                    errorView = (TLCErrorView) UIHelper.openView(TLCErrorView.ID);
                } else
                {
                    errorView = (TLCErrorView) UIHelper.findView(TLCErrorView.ID);
                }
                if (errorView != null)
                {
                    errorView.fill(errors);

                    if (errors.size() == 0)
                    {
                        errorView.hide();
                    }
                }
            }
        });

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

        public Color getBackground(Object element)
        {
            return null;
        }

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
            stateImage.dispose();
            varImage.dispose();
            recordImage.dispose();
            super.dispose();
        }

    }

    
    
    
}
