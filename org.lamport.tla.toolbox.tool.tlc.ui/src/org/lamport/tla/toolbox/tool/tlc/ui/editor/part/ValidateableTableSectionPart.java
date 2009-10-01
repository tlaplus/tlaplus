package org.lamport.tla.toolbox.tool.tlc.ui.editor.part;

import java.util.Vector;

import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TableViewer;
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
import org.eclipse.ui.forms.widgets.Section;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.BasicFormPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.provider.FormulaContentProvider;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.wizard.FormulaWizard;

/**
 * Section part with table and add, edit and remove buttons
 * @author Simon Zambrovski
 * @version $Id: TableSectionPart.java 625 2009-04-07 04:04:58Z simonzam $
 */
public class ValidateableTableSectionPart extends SectionPart implements IValidateble
{
    private BasicFormPage page;
    protected TableViewer tableViewer;
    private Button buttonAdd;
    private Button buttonEdit;
    private Button buttonRemove;

    // a listener reacting on clicks
    protected SelectionListener fSelectionListener = new SelectionAdapter() {
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
    protected ISelectionChangedListener fSelectionChangedListener = new ISelectionChangedListener() {
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
     * @see ValidateableTableSectionPart#TableSectionPart(Composite, String, String, FormToolkit, int)
     */
    public ValidateableTableSectionPart(Composite composite, String title, String description, FormToolkit toolkit,
            BasicFormPage page, String sectionName)
    {
        this(composite, title, description, toolkit, Section.DESCRIPTION | Section.TITLE_BAR, page, sectionName);
    }

    /**
     * Constructs the section part
     * @param composite, parent composite
     * @param title, part title
     * @param description, part description
     * @param toolkit, a toolkit for building controls
     * @param sectionFlags, flags to be passed to the part during construction
     * @param sectionName name of the section 
     */
    public ValidateableTableSectionPart(Composite composite, String title, String description, FormToolkit toolkit,
            int sectionFlags, BasicFormPage page, String sectionName)
    {
        super(FormHelper.createSectionComposite(composite, title, description, toolkit, sectionFlags, null));
        this.page = page;
        page.getDataBindingManager().bindSection(this, sectionName, page.getId());
    }

    /**
     * Initialize the section
     */
    public void initialize(IManagedForm form)
    {
        super.initialize(form);
        sectionInitialize(form.getToolkit());
    }

    public void commit(boolean onSave)
    {
        // commit the part on save, but not on other events
        if (onSave)
        {
            super.commit(onSave);
        }
    }

    /**
     * Constructs the section content
     * @param toolkit
     */
    protected void sectionInitialize(FormToolkit toolkit)
    {
        GridData gd;

        // create the composite
        Composite sectionArea = (Composite) getSection().getClient();
        sectionArea.setLayout(new GridLayout(2, false));
        // The section grabs the entire space
        gd = new GridData(GridData.FILL_BOTH);
        gd.grabExcessVerticalSpace = true;
        getSection().setLayoutData(gd);

        // create the table
        Table table = createTable(sectionArea, toolkit);
        // The table grabs the entire space in the section
        gd = new GridData(GridData.FILL_BOTH);
        gd.grabExcessHorizontalSpace = true;
        gd.grabExcessVerticalSpace = true;
        // span for the buttons
        gd.verticalSpan = 3;
        table.setLayoutData(gd);

        // create the table viewer
        tableViewer = createTableViewer(table);

        // create buttons
        createButtons(sectionArea, toolkit, true, true, true);

        // setup the buttons
        changeButtonEnablement();
    }

    /**
     * @param table
     * @return
     */
    protected TableViewer createTableViewer(Table table)
    {
        // create
        CheckboxTableViewer tableViewer = new CheckboxTableViewer(table);
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

        // mark model dirty on checking / un-checking
        tableViewer.addCheckStateListener(new ICheckStateListener() {
            public void checkStateChanged(CheckStateChangedEvent event)
            {
                doCheck();
            }
        });

        return tableViewer;
    }

    /**
     * Creates the table to be put into the tableviewer
     * @param sectionArea
     * @return
     */
    protected Table createTable(Composite sectionArea, FormToolkit toolkit)
    {
        Table table = toolkit.createTable(sectionArea, SWT.MULTI | SWT.CHECK | SWT.V_SCROLL | SWT.H_SCROLL
                | SWT.FULL_SELECTION);
        table.setLinesVisible(false);
        table.setHeaderVisible(false);
        return table;
    }

    /**
     * Creates buttons
     * <br>
     * Subclasses might override this method if they intend to change the buttons. For actual implementation see 
     * {@link ValidateableTableSectionPart#doCreateButtons(Composite, FormToolkit, boolean, boolean, boolean)} 
     */
    protected void createButtons(Composite sectionArea, FormToolkit toolkit, boolean add, boolean edit, boolean remove)
    {
        doCreateButtons(sectionArea, toolkit, add, edit, remove);
    }

    /**
     * Create up to three buttons in the section area
     * @param sectionArea
     * @param toolkit
     * @param add
     * @param edit
     * @param remove
     */
    protected void doCreateButtons(Composite sectionArea, FormToolkit toolkit, boolean add, boolean edit, boolean remove)
    {
        GridData gd;
        int added = 0;
        if (add)
        {
            // add button
            buttonAdd = toolkit.createButton(sectionArea, "Add", SWT.PUSH);
            buttonAdd.addSelectionListener(fSelectionListener);
            gd = new GridData();
            gd.verticalAlignment = SWT.TOP;
            gd.widthHint = 70;
            buttonAdd.setLayoutData(gd);
            added++;
        }

        if (edit)
        {
            // edit button
            buttonEdit = toolkit.createButton(sectionArea, "Edit", SWT.PUSH);
            buttonEdit.addSelectionListener(fSelectionListener);
            gd = new GridData();
            gd.verticalAlignment = SWT.TOP;
            gd.widthHint = 70;
            buttonEdit.setLayoutData(gd);
            added++;
        }

        if (remove)
        {
            // remove button
            buttonRemove = toolkit.createButton(sectionArea, "Remove", SWT.PUSH);
            buttonRemove.addSelectionListener(fSelectionListener);
            gd = new GridData();
            gd.verticalAlignment = SWT.TOP;
            gd.widthHint = 70;
            buttonRemove.setLayoutData(gd);
            added++;
        }

        if (added < 3)
        {
            Composite span = toolkit.createComposite(sectionArea);
            gd = new GridData();
            gd.verticalSpan = 3 - added;
            gd.verticalAlignment = SWT.TOP;
            gd.widthHint = 70;
            span.setLayoutData(gd);
        }
    }

    /**
     * Retrieves the table viewer
     * @return
     */
    public TableViewer getTableViewer()
    {
        return tableViewer;
    }

    /**
     * Remove the selected formulas
     */
    protected void doRemove()
    {
        IStructuredSelection selection = (IStructuredSelection) tableViewer.getSelection();
        Vector input = (Vector) tableViewer.getInput();
        input.removeAll(selection.toList());
        tableViewer.setInput(input);
        this.doMakeDirty();
    }

    /**
     * Add a formula to the list
     */
    protected void doAdd()
    {
        Formula formula = doEditFormula(null);

        // add a formula
        if (formula != null)
        {
            Vector input = ((Vector) tableViewer.getInput());
            input.add(formula);
            tableViewer.setInput(input);
            if (tableViewer instanceof CheckboxTableViewer)
            {
                ((CheckboxTableViewer) tableViewer).setChecked(formula, true);
            }
            this.doMakeDirty();
        }
    }

    /**
     * Edit selected formula 
     */
    protected void doEdit()
    {
        IStructuredSelection selection = (IStructuredSelection) tableViewer.getSelection();
        Formula formula = (Formula) selection.getFirstElement();
        Formula editedFormula = doEditFormula(formula);
        if (editedFormula != null)
        {
            formula.setFormula(editedFormula.getFormula());
            if (tableViewer instanceof CheckboxTableViewer)
            {
                ((CheckboxTableViewer) tableViewer).setChecked(formula, true);
            }
            this.doMakeDirty();
            tableViewer.refresh();
        }
    }

    /**
     * React on formula been checked or un-checked
     */
    protected void doCheck()
    {
        this.doMakeDirty();
    }

    /**
     * 
     */
    protected void changeButtonEnablement()
    {
        IStructuredSelection selection = (IStructuredSelection) tableViewer.getSelection();

        if (buttonRemove != null)
        {
            buttonRemove.setEnabled(!selection.isEmpty());
        }
        if (buttonEdit != null)
        {
            buttonEdit.setEnabled(selection.size() == 1);
        }
    }

    /**
     * Opens a dialog for formula processing and returns the edited formula  
     * @param formula initial formula, can be <code>null</code>
     * @return result of editing or <code>null</code>, if editing canceled
     */
    protected Formula doEditFormula(Formula formula)
    {
        // Create the wizard
        FormulaWizard wizard = new FormulaWizard(getSection().getText(), getSection().getDescription());
        wizard.setFormula(formula);

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

    /**
     * Marks the part dirty and hooks the validation method of the page
     */
    protected void doMakeDirty()
    {
        this.validate();
        this.markDirty();
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.ui.editor.validator.IValidateble#validate(org.eclipse.jface.text.IDocument, org.eclipse.jface.text.IDocument)
     */
    public void validate()
    {
        page.validatePage(false);
    }
}
