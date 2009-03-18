package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.util.Vector;

import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Table;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.SectionPart;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.FormulaContentProvider.Formula;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.wizard.FormulaWizard;

/**
 * Section part with table and add, edit and remove buttons
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TableSectionPart extends SectionPart
{
    private CheckboxTableViewer tableViewer;
    private Button buttonAdd;
    private Button buttonEdit;
    private Button buttonRemove;

    // a listener reacting on clicks
    private SelectionListener fSelectionListener = new SelectionAdapter() {
        public void widgetSelected(SelectionEvent e)
        {
            Object source = e.getSource();
            if (source == buttonAdd)
            {
                doAdd();
            } else if (source == buttonRemove)
            {
                doRemove();
            } else if (source == buttonEdit)
            {
                doEdit();
            }
        }
    };
    
    // a listener reacting on selection in the table viewer
    private ISelectionChangedListener fSelectionChangedListener = new ISelectionChangedListener() {
        public void selectionChanged(SelectionChangedEvent event)
        {
            Object source = event.getSource();
            if (source == tableViewer)
            {
                changeButtonEnablement();
            }
        }
    };

    /**
     * Constructor of the part without section flags
     * @see TableSectionPart#TableSectionPart(Composite, String, String, FormToolkit, int)
     */
    public TableSectionPart(Composite composite, String title, String description, FormToolkit toolkit)
    {
        super(FormHelper.createSectionComposite(composite, title, description, toolkit));
    }

    /**
     * Constructs the section part
     * @param composite, parent composite
     * @param title, part title
     * @param description, part description
     * @param toolkit, a toolkit for building controls
     * @param sectionFlags, flags to be passed to the part during construction
     */
    public TableSectionPart(Composite composite, String title, String description, FormToolkit toolkit, int sectionFlags)
    {
        super(FormHelper.createSectionComposite(composite, title, description, toolkit, sectionFlags, null));
    }

    /**
     * Initialize the section
     */
    public void initialize(IManagedForm form)
    {
        super.initialize(form);
        sectionInitialize(form.getToolkit());
    }

    /**
     * Constructs the section content
     * @param toolkit
     */
    protected void sectionInitialize(FormToolkit toolkit)
    {
        GridData gd;

        Composite sectionArea = (Composite) getSection().getClient();
        sectionArea.setLayout(new GridLayout(2, false));

        Table table = toolkit.createTable(sectionArea, SWT.MULTI | SWT.CHECK | SWT.V_SCROLL | SWT.H_SCROLL);

        // The section grabs the entire space
        gd = new GridData(GridData.FILL_BOTH);
        gd.grabExcessVerticalSpace = true;
        getSection().setLayoutData(gd);

        // The table grabs the entire space
        gd = new GridData(GridData.FILL_BOTH);
        gd.grabExcessHorizontalSpace = true;
        gd.grabExcessVerticalSpace = true;
        // span for the buttons
        gd.verticalSpan = 3;

        table.setLayoutData(gd);
        table.setLinesVisible(false);
        table.setHeaderVisible(false);

        tableViewer = new CheckboxTableViewer(table);
        // represent formulas in the view
        tableViewer.setContentProvider(new FormulaContentProvider());
        // on changed selection change button enablement
        tableViewer.addSelectionChangedListener(fSelectionChangedListener);
        // edit on double-click
        tableViewer.addDoubleClickListener(new IDoubleClickListener() {
            public void doubleClick(DoubleClickEvent event)
            {
                doEdit();
            }
        });

        // add button
        buttonAdd = toolkit.createButton(sectionArea, "Add", SWT.PUSH);
        buttonAdd.addSelectionListener(fSelectionListener);
        gd = new GridData();
        gd.verticalAlignment = SWT.TOP;
        gd.widthHint = 70;
        buttonAdd.setLayoutData(gd);

        // edit button
        buttonEdit = toolkit.createButton(sectionArea, "Edit", SWT.PUSH);
        buttonEdit.addSelectionListener(fSelectionListener);
        gd = new GridData();
        gd.verticalAlignment = SWT.TOP;
        gd.widthHint = 70;
        buttonEdit.setLayoutData(gd);

        // remove button
        buttonRemove = toolkit.createButton(sectionArea, "Remove", SWT.PUSH);
        buttonRemove.addSelectionListener(fSelectionListener);
        gd = new GridData();
        gd.verticalAlignment = SWT.TOP;
        gd.widthHint = 70;
        buttonRemove.setLayoutData(gd);

        // setup the buttons
        changeButtonEnablement();
    }


    /**
     * Retrieves the table viewer
     * @return
     */
    public CheckboxTableViewer getTableViewer()
    {
        return tableViewer;
    }

    /**
     * Remove the selected formulas
     */
    private void doRemove()
    {
        IStructuredSelection selection = (IStructuredSelection) tableViewer.getSelection();
        Vector input = (Vector)tableViewer.getInput();
        input.removeAll(selection.toList());
        tableViewer.setInput(input);
        this.markDirty();
        
    }

    /**
     * Add a formula to the list
     */
    private void doAdd()
    {
        String formulaString = doEditFormula(null);

        // add a formula
        if (formulaString != null)
        {
            Formula formula = new Formula(formulaString);
            
            Vector input = ((Vector)tableViewer.getInput());
            input.add(formula);
            tableViewer.setInput(input);
            tableViewer.setChecked(formula, true);
            this.markDirty();
        }
    }

    /**
     * Edit selected formula 
     */
    protected void doEdit()
    {
        IStructuredSelection selection = (IStructuredSelection) tableViewer.getSelection();
        Formula formula = (Formula) selection.getFirstElement();
        String editedFormula = doEditFormula(formula.formula);
        if (editedFormula != null)
        {
            formula.formula = editedFormula;
            tableViewer.setChecked(formula, true);
            this.markDirty();
            tableViewer.refresh();
        }
    }

    /**
     * 
     */
    protected void changeButtonEnablement()
    {
        IStructuredSelection selection = (IStructuredSelection) tableViewer.getSelection();

        buttonRemove.setEnabled(!selection.isEmpty());
        buttonEdit.setEnabled(selection.size() == 1);
    }

    /**
     * Opens a dialog for formula processing and returns the edited formula  
     * @param formulaString initial formula, can be <code>null</code>
     * @return result of editing or <code>null</code>, if editing cancelled
     */
    private String doEditFormula(String formulaString)
    {
        // Create the wizard
        FormulaWizard wizard = new FormulaWizard(getSection().getText(), getSection().getDescription());
        wizard.setFormula(formulaString);

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
}
