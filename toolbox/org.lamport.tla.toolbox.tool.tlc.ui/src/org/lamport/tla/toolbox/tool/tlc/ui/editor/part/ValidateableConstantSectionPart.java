package org.lamport.tla.toolbox.tool.tlc.ui.editor.part;

import java.util.Vector;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Table;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.BasicFormPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.provider.AssignmentContentProvider;
import org.lamport.tla.toolbox.tool.tlc.ui.wizard.AssignmentWizard;
import org.lamport.tla.toolbox.tool.tlc.ui.wizard.AssignmentWizardPage;

import tlc2.model.Assignment;

/**
 * Section part for the constants 
 * @author Simon Zambrovski
 */
public class ValidateableConstantSectionPart extends ValidateableTableSectionPart
{
    public ValidateableConstantSectionPart(Composite composite, String title, String description, FormToolkit toolkit,
            int flags, BasicFormPage page, String sectionName)
    {
        super(composite, title, description, toolkit, flags, page, sectionName);
    }

    protected Assignment doEditFormula(Assignment formula) // gets called when editing a constant and ...
    {
        Assert.isNotNull(formula);

        // Create the wizard
        AssignmentWizard wizard = new AssignmentWizard(getSection().getText(), getSection().getDescription(),
                (Assignment) formula, AssignmentWizard.SHOW_OPTION, AssignmentWizardPage.CONSTANT_WIZARD_ID);
        // Create the wizard dialog
        WizardDialog dialog = new WizardDialog(getTableViewer().getTable().getShell(), wizard);
        wizard.setWizardDialog(dialog);
        dialog.setHelpAvailable(true);

        // Open the wizard dialog
        if (Window.OK == dialog.open())
        {
            return wizard.getFormula();
        } else
        {
            return null;  // We get here if the user cancels.
        }
    }

    /**
     * Add assignment to the list -- Despite Simon's comments, this is actually called when clicking on ADD 
     * for  Definition Override
     */
    @Override
    @SuppressWarnings("unchecked")  // Generic casting...
    protected void doAdd()
    {
        Assignment formula = doEditFormula((Assignment) null);

        // add a formula
        if (formula != null)
        {
            Vector<Assignment> input = ((Vector<Assignment>) tableViewer.getInput()); // this seems to be the place to check for duplicate overrides.
            input.add(formula);
            tableViewer.setInput(input);
            this.doMakeDirty();
        }
    }

    // This is called when hitting EDIT or double clicking to enter a Constant's value or to change a Definition override.
    @Override
    protected void doEdit()  
    {
        IStructuredSelection selection = (IStructuredSelection) tableViewer.getSelection();
        Assignment formula = (Assignment) selection.getFirstElement();
        if (formula == null) {
        	// User clicked on an empty line in the formula table
        	return;	
        }
        Assignment editedFormula = doEditFormula(formula);
        if (editedFormula != null)
        {
            formula.setParams(editedFormula.getParams());
            formula.setRight(editedFormula.getRight());
            super.doMakeDirty();
            tableViewer.refresh();
        }
    }

    /**
     * create the viewer
     */
    @Override
    protected TableViewer createTableViewer(Table table)
    {
        // create
        TableViewer tableViewer = new TableViewer(table);
        // represent formulas in the view
        tableViewer.setContentProvider(new AssignmentContentProvider());
        // on changed selection change button enablement
        tableViewer.addSelectionChangedListener(fSelectionChangedListener);
        // edit on double-click
        tableViewer.addDoubleClickListener(new IDoubleClickListener() {
            public void doubleClick(DoubleClickEvent event)
            {
                doEdit();
            }
        });

        return tableViewer;
    }

    /**
     * create the table (no check boxes)
     */
    @Override
    protected Table createTable(Composite sectionArea, FormToolkit toolkit)
    {
        Table table = toolkit.createTable(sectionArea, SWT.MULTI | SWT.V_SCROLL | SWT.H_SCROLL | SWT.FULL_SELECTION);
        table.setLinesVisible(false);
        table.setHeaderVisible(false);
        return table;
    }

    /**
     * Only create the edit button
     */
    @Override
    protected void createButtons(Composite sectionArea, FormToolkit toolkit, boolean add, boolean edit, boolean remove)
    {
        doCreateButtons(sectionArea, toolkit, false, true, false);
    }
}
