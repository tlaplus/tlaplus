package org.lamport.tla.toolbox.tool.tlc.ui.dialog;

import java.util.Comparator;
import java.util.List;
import java.util.Vector;

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
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;

/**
 * Filter dialog for selection of definitions 
 * @author Simon Zambrovski
 * @version $Id$
 * 
 * This seems to be implementing the Definition Override section of the Advanced Options model 
 * page.
 * 
 * Modified on 5 July 2010 by LL not to allow the same definition to be overridden more
 * than once.  This required adding a private field, set by the constructor, that equals the array
 * of all names of already overridden operators, and modifying the fillContentProvider method
 * so it did not add those operator definitions to the dialog.  See the constructor comments for
 * more details.
 */
public class FilteredDefinitionSelectionDialog extends FilteredItemsSelectionDialog
{
    // setting id
    private static final String SETTINGS = "org.lamport.tla.toolbox.tool.tlc.ui.dialog.FilteredDefinitionSelectionDialog";
    // specification handle
    private SpecObj specObj;
    // the names of all operators that have already been overridden.
    // These are the names by which they are known to the root module, such
    // as "frob!bar!id".
    private String[] names;

    /**
     * Constructs new dialog instance
     * @param shell shell to open dialog
     * @param multi true if multiple selection should be allowed
     * @param specObj the specObject holding the content
     * @param names the names of all operators that have already been overridden.
     *        These are the names by which they are known to the root module, such
     *        as "frob!bar!id". 
     */
    public FilteredDefinitionSelectionDialog(Shell shell, boolean multi, SpecObj specObj, String[] names)
    {
        super(shell, multi);
        this.specObj = specObj;
        setListLabelProvider(getListLabelProvider());
        setDetailsLabelProvider(getDetailLabelProvider());
        setSelectionHistory(new DefinitionHistory());
        this.names = names;
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

                    return node.getSource().getName().toString()
                            + ((node.getSource().getOriginallyDefinedInModuleNode() != null) ? " : "
                                    + node.getSource().getOriginallyDefinedInModuleNode().getName().toString() : "");
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
                    if (node.getSource() == node)
                    {
                        return node.getName().toString();
                    } else
                    {
                        return node.getSource().getName().toString() + " ["
                                + node.getSource().getOriginallyDefinedInModuleNode().getName().toString() + "]";
                    }
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
     * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#fillContentProvider(org.eclipse.ui.dialogs.FilteredItemsSelectionDialog.AbstractContentProvider, 
     *   org.eclipse.ui.dialogs.FilteredItemsSelectionDialog.ItemsFilter, 
     *    org.eclipse.core.runtime.IProgressMonitor)
     *    
     * This raised a null-pointer exception if it was called when the spec is unparsed,
     * because then specObj is null.  I hacked a fix to this, but I think
     * there are more bugs lurking because the user can edit the model when the spec
     * is unparsed.  LL 20 Sep 2009  

     * Here is what I learned when trying to figure out how to get hold of the names of already-overridden
     * operators, which are now contained in this.names.  When the model is saved, these names are
     * saved as an attribute for an ILaunchConfiguration object.
     *  
     * TLCModelLaunchDelegate.buildForLaunch gets hold of the names by calling
     *  
     *    ModelHelper.deserializeAssignmentList(config.getAttribute(MODEL_PARAMETER_DEFINITIONS,
     *              new Vector()))
     *              
     *  where config is an ILaunchConfiguration passed in as an argument.  But 
     *  buildForLaunch is called from deep inside the  bowels of the Eclipse code, and I
     *  don't know how the ILaunchConfiguration is given to the Eclipse code.
     *  
     *  AdvancedModelPage.loadData() gets the names  by 
     *  
     *     List definitions = getConfig().getAttribute(MODEL_PARAMETER_DEFINITIONS, new Vector());
     *
     *  where getConfig() is in BasicFormPage, which AdvancedModelPage extends.  But of course,
     *  by the time we're down in this method, we've lost all information about what page
     *  we're working on.
     *  
     *  However, that list doesn't contain the names of definitions that have been overridden
     *  since the model was last saved.  Those are held by the TableViewer that is created
     *  by the ValidateableOverridesSectionPart through its supersupersuperclass
     *  org.eclipse.ui.forms.SectionPart.
     *  
     */
    protected void fillContentProvider(AbstractContentProvider contentProvider, ItemsFilter itemsFilter,
            IProgressMonitor progressMonitor) throws CoreException
    {
        if (specObj == null)
        {
            return;
        }
        OpDefNode[] opDefs = specObj.getExternalModuleTable().getRootModule().getOpDefs();
        progressMonitor.beginTask("Looking up for definitions...", opDefs.length);

        for (int i = 0; i < opDefs.length; i++)
        {
            if (isNotInArray(opDefs[i].getName().toString(), this.names)) {
            contentProvider.add(opDefs[i], itemsFilter);
            progressMonitor.worked(1);
            }
        }
        progressMonitor.done();
    }
    
    /**
     * Returns true iff str is not an element of array.
     * 
     * @param str
     * @param array
     * @return
     */
    private boolean isNotInArray(String str, String[] array) {
        for (int i = 0; i < array.length; i++) {
            if (str.equals(array[i])) {
                return false;
            }
        }
        return true;
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#getElementName(java.lang.Object)
     */
    // This is used to check for duplicates. Currently, duplicates still appear for some reason.
    public String getElementName(Object item)
    {
        OpDefNode node = (OpDefNode) item;
        return node.getSource().getName().toString()
                + node.getSource().getOriginallyDefinedInModuleNode().getName().toString();
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#getItemsComparator()
     */
    protected Comparator getItemsComparator()
    {
        return new Comparator() {
            // group by modules, sort by user modules first, then by module name and then then by operator name
            public int compare(Object arg0, Object arg1)
            {
                OpDefNode node0 = (OpDefNode) arg0;
                OpDefNode node1 = (OpDefNode) arg1;

                ModuleNode module0 = node0.getOriginallyDefinedInModuleNode();
                ModuleNode module1 = node1.getOriginallyDefinedInModuleNode();

                boolean module0user = ToolboxHandle.isUserModule(module0.getName().toString());
                boolean module1user = ToolboxHandle.isUserModule(module1.getName().toString());

                if (module0user)
                {
                    // module 0 is a user module
                    if (module1user)
                    {
                        // both are user
                    } else
                    {
                        // module 1 is a standard module
                        return -1;
                    }
                } else
                {
                    // module 0 is not a user module
                    if (module1user)
                    {
                        // module 1 is a user module
                        return 1;
                    } else
                    {
                        // none are user modules
                    }
                }

                // at this point both modules are user modules, or both are standard modules
                // compare based on the name

                int moduleCompare = module0.getName().toString().compareToIgnoreCase(module1.getName().toString());
                if (moduleCompare == 0)
                {
                    return node0.getName().toString().compareToIgnoreCase(node1.getName().toString());
                } else
                {
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

        // matches item based on name of the source of the definition node
        // because this is what appears in the selection dialog
        public boolean matchItem(Object item)
        {

            if (getPattern() == null || getPattern().length() == 0)
            {
                return true;
            }
            return matches(((OpDefNode) item).getSource().getName().toString());
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
