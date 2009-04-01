package org.lamport.tla.toolbox.tool.tlc.ui.editor;

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
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.ui.wizard.ConstantWizard;

/**
 * Section part for the constants 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ConstantSectionPart extends TableSectionPart
{
    /**
     * @param composite
     * @param title
     * @param description
     * @param toolkit
     */
    public ConstantSectionPart(Composite composite, String title, String description, FormToolkit toolkit)
    {
        super(composite, title, description, toolkit);
    }

    protected Assignment doEditFormula(Assignment formula)
    {
        Assert.isNotNull(formula);
        
        // Create the wizard
        ConstantWizard wizard = new ConstantWizard(getSection().getText(), getSection().getDescription(), (Assignment) formula);
        // Create the wizard dialog
        WizardDialog dialog = new WizardDialog(getTableViewer().getTable().getShell(), wizard);
        dialog.setHelpAvailable(true);

        // Open the wizard dialog
        if (Window.OK == dialog.open())
        {
            return wizard.getFormula();
        } else
        {
            return null;
        }
    }

    protected void doEdit()
    {
        IStructuredSelection selection = (IStructuredSelection) tableViewer.getSelection();
        Assignment formula = (Assignment) selection.getFirstElement();
        Assignment editedFormula = doEditFormula(formula);
        if (editedFormula != null)
        {
            formula.setParams(editedFormula.getParams());
            formula.setRight(editedFormula.getRight());
            this.markDirty();
            tableViewer.refresh();
        }
    }
    
    /**
     * create the viewer
     */
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
    protected Table createTable(Composite sectionArea, FormToolkit toolkit)
    {
        Table table = toolkit.createTable(sectionArea, SWT.MULTI | SWT.V_SCROLL | SWT.H_SCROLL);
        table.setLinesVisible(false);
        table.setHeaderVisible(false);
        return table;
    }

    /**
     * Only create the edit button
     */
    protected void createButtons(Composite sectionArea, FormToolkit toolkit, boolean add, boolean edit, boolean remove)
    {
        super.createButtons(sectionArea, toolkit, false, true, false);
    }
}
