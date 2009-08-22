package org.lamport.tla.toolbox.tool.tlc.ui.view;

import java.util.List;
import java.util.Vector;

import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.ui.part.ViewPart;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCSetOrSeqVariableValue;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCSetVariableValue;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCSimpleVariableValue;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCState;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCVariable;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.data.TLCVariableValue;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Basic view for state trace exploring
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TraceExplorer extends ViewPart
{

    public static final String ID = "toolbox.tool.tlc.view.TraceExplorer";
    protected static final IDocument EMPTY_DOCUMENT = new Document("");
    private SashForm sashForm;
    private SourceViewer valueViewer;
    private TreeViewer variableViewer;

    public void createPartControl(Composite parent)
    {
        sashForm = new SashForm(parent, SWT.VERTICAL);

        Tree tree = new Tree(sashForm, SWT.V_SCROLL | SWT.BORDER | SWT.FULL_SELECTION | SWT.SINGLE);
        tree.setHeaderVisible(true);
        tree.setLinesVisible(true);

        GridData gd = new GridData(SWT.LEFT, SWT.TOP, true, false);
        gd.grabExcessHorizontalSpace = true;
        gd.minimumHeight = 300;
        gd.minimumWidth = 300;

        tree.setLayoutData(gd);

        for (int i = 0; i < StateLabelProvider.COLUMN_TEXTS.length; i++)
        {
            TreeColumn column = new TreeColumn(tree, SWT.LEFT);
            column.setText(StateLabelProvider.COLUMN_TEXTS[i]);
            column.setWidth(StateLabelProvider.COLUMN_WIDTH[i]);
        }

        variableViewer = new TreeViewer(tree);
        variableViewer.setContentProvider(new StateContentProvider());
        variableViewer.setLabelProvider(new StateLabelProvider());
        variableViewer.addSelectionChangedListener(new ISelectionChangedListener() {

            public void selectionChanged(SelectionChangedEvent event)
            {
                if (!((IStructuredSelection) event.getSelection()).isEmpty())
                {
                    Object selection = ((IStructuredSelection) event.getSelection()).getFirstElement();
                    valueViewer.setDocument(new Document(selection.toString()));
                } else
                {

                    valueViewer.setDocument(EMPTY_DOCUMENT);
                }

            }
        });

        // sashForm.setMaximizedControl(tree);

        valueViewer = FormHelper.createSourceViewer(sashForm, SWT.V_SCROLL | SWT.MULTI | SWT.BORDER);
        valueViewer.setEditable(false);
        gd = new GridData(SWT.LEFT, SWT.TOP, true, false);
        gd.grabExcessHorizontalSpace = true;
        valueViewer.getControl().setLayoutData(gd);
    }

    public void fill(List trace)
    {
        variableViewer.setInput(trace);
    }
    
    public void clear()
    {
        variableViewer.setInput(new Vector());
    }

    public void setFocus()
    {
        variableViewer.getTree().setFocus();
    }

    /**
     * Content provider for the tree table  
     */
    static class StateContentProvider implements ITreeContentProvider
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
                if (value instanceof TLCSetOrSeqVariableValue) 
                {
                    return ((TLCSetOrSeqVariableValue)value).getElements();
                }
                return null;
            } else if (parentElement instanceof TLCVariableValue) 
            {
                TLCVariableValue value = (TLCVariableValue) parentElement;
                if (value instanceof TLCSetOrSeqVariableValue) 
                {
                    return ((TLCSetOrSeqVariableValue)value).getElements();
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

    /**
     * Label provider for the tree table
     */
    static class StateLabelProvider extends LabelProvider implements ITableLabelProvider
    {
        public static final int NAME = 0;
        public static final int VALUE = 1;

        public static final int[] COLUMN_WIDTH = { 200, 200 };
        public static final String[] COLUMN_TEXTS = { "Name", "Value" };

        private Image stateImage;
        private Image varImage;

        public StateLabelProvider()
        {
            stateImage = TLCUIActivator.getImageDescriptor("/icons/full/default_co.gif").createImage();
            varImage = TLCUIActivator.getImageDescriptor("/icons/full/private_co.gif").createImage();
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
            } else if (element instanceof TLCSetOrSeqVariableValue || element instanceof TLCSimpleVariableValue) 
            {
                TLCVariableValue varValue = (TLCVariableValue) element;
                switch (columnIndex) {
                case VALUE:
                    return varValue.toString();
                case NAME:
                default:
                    break;
                }
            }
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
            super.dispose();
        }

    }

    public void hide()
    {
        UIHelper.runUIAsync(new Runnable() {
            public void run()
            {
                getViewSite().getPage().hideView(TraceExplorer.this);
            }
        });
    }

}
