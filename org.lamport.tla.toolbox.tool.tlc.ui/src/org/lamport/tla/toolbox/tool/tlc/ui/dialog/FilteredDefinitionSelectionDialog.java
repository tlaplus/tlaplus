package org.lamport.tla.toolbox.tool.tlc.ui.dialog;

import java.util.Comparator;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.IDialogSettings;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IMemento;
import org.eclipse.ui.dialogs.FilteredItemsSelectionDialog;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;

/**
 * Filter dialog for selection of definitions 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class FilteredDefinitionSelectionDialog extends FilteredItemsSelectionDialog
{
    // setting id
    private static final String SETTINGS = FilteredDefinitionSelectionDialog.class.getCanonicalName();
    // specification handle
    private SpecObj specObj;

    /**
     * Constructs new dialog instance
     * @param shell shell to open dialog
     * @param multi true if multiple selection should be allowed
     * @param specObj the specObject holding the content
     */
    public FilteredDefinitionSelectionDialog(Shell shell, boolean multi, SpecObj specObj)
    {
        super(shell, multi);
        this.specObj = specObj;
        setListLabelProvider(getListLabelProvider());
        setDetailsLabelProvider(getDetailLabelProvider());
        setSelectionHistory(new DefinitionHistory());
    }

    /**
     * Creates a label provider for the detail section below the list<br>
     * The label provider prints out the name of operation definition and the module the operation is defined in 
     */
    private ILabelProvider getDetailLabelProvider()
    {
        return new LabelProvider() {
            public String getText(Object element)
            {
                if (element instanceof OpDefNode)
                {
                    OpDefNode node = (OpDefNode) element;
                    
                    return node.getName().toString()
                            + ((node.getOriginallyDefinedInModuleNode() != null) ? " : "
                                    + node.getOriginallyDefinedInModuleNode().getName().toString() : "");
                }
                return super.getText(element);
            }
        };
    }

    /**
     * Creates label provider for the elements in the list
     */
    private ILabelProvider getListLabelProvider()
    {
        return new LabelProvider() {
            public String getText(Object element)
            {
                if (element instanceof OpDefNode)
                {
                    OpDefNode node = (OpDefNode) element;
                    return node.getName().toString();
                }
                return super.getText(element);
            }
        };
    }


    /* (non-Javadoc)
     * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#createFilter()
     */
    protected ItemsFilter createFilter()
    {
        return new DefinitionFilter();
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#fillContentProvider(org.eclipse.ui.dialogs.FilteredItemsSelectionDialog.AbstractContentProvider, org.eclipse.ui.dialogs.FilteredItemsSelectionDialog.ItemsFilter, org.eclipse.core.runtime.IProgressMonitor)
     */
    protected void fillContentProvider(AbstractContentProvider contentProvider, ItemsFilter itemsFilter,
            IProgressMonitor progressMonitor) throws CoreException
    {

        OpDefNode[] opDefs = specObj.getExternalModuleTable().getRootModule().getOpDefs();
        progressMonitor.beginTask("Looking up for definitions...", opDefs.length);

        for (int i = 0; i < opDefs.length; i++)
        {
            contentProvider.add(opDefs[i], itemsFilter);
            progressMonitor.worked(1);
        }
        progressMonitor.done();
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#getElementName(java.lang.Object)
     */
    public String getElementName(Object item)
    {
        OpDefNode node = (OpDefNode) item;
        return node.getName().toString();
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#getItemsComparator()
     */
    protected Comparator getItemsComparator()
    {
        return new Comparator() {

            // group by modules, sort by operator name
            public int compare(Object arg0, Object arg1)
            {
                OpDefNode node0 = (OpDefNode) arg0;
                OpDefNode node1 = (OpDefNode) arg1;
                
                ModuleNode module0 = node0.getOriginallyDefinedInModuleNode();
                ModuleNode module1 = node1.getOriginallyDefinedInModuleNode();
                
                int moduleCompare = module0.getName().toString().compareTo(module1.getName().toString());
                if (moduleCompare == 0) 
                {
                    return node0.getName().toString().compareTo(node1.getName().toString());
                } else {
                    return moduleCompare;
                }
            }

        };
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#validateItem(java.lang.Object)
     */
    protected IStatus validateItem(Object item)
    {
        return Status.OK_STATUS;
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#getDialogSettings()
     */
    protected IDialogSettings getDialogSettings()
    {
        IDialogSettings settings = TLCUIActivator.getDefault().getDialogSettings().getSection(SETTINGS);
        if (settings == null)
        {
            settings = TLCUIActivator.getDefault().getDialogSettings().addNewSection(SETTINGS);
        }
        return settings;
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#createExtendedContentArea(org.eclipse.swt.widgets.Composite)
     */
    protected Control createExtendedContentArea(Composite parent)
    {
        // TODO Auto-generated method stub
        return null;
    }


    /**
     * Filters definitions 
     */
    public class DefinitionFilter extends ItemsFilter
    {

        public boolean isConsistentItem(Object item)
        {
            return true;
        }

        public boolean matchItem(Object item)
        {

            if (getPattern().isEmpty() || getPattern() == null)
            {
                return true;
            }
            return matches(((OpDefNode) item).getName().toString());
        }
    }

    /**
     * Takes care of remembering selected items
     * not implemented yet  
     */
    public class DefinitionHistory extends SelectionHistory
    {

        protected Object restoreItemFromMemento(IMemento element)
        {
            return null;
        }

        protected void storeItemToMemento(Object item, IMemento element)
        {
        }
    }
}
