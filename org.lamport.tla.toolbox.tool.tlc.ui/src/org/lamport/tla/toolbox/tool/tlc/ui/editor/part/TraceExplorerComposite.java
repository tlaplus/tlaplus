package org.lamport.tla.toolbox.tool.tlc.ui.editor.part;

import java.util.Vector;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.DoubleClickEvent;
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
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.provider.FormulaContentProvider;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;
import org.lamport.tla.toolbox.tool.tlc.ui.wizard.FormulaWizard;

/**
 * This is somewhat mislabeled as a composite. Its really
 * a wrapper class for a section.
 * 
 * This contains a section which contains a table that is populated
 * with items that have a checkbox next to them to indicate if they should
 * be used in the run of the trace explorer.
 * 
 * There are five buttons to the right of the table: Add, Remove, Edit, Explore, and Restore.
 * Explore launches the trace explorer and restore restores the old trace without any expressions
 * from the trace explorer section.
 * 
 * @author drickett
 *
 */
public class TraceExplorerComposite
{
    protected TableViewer tableViewer;
    private Button buttonAdd;
    private Button buttonEdit;
    private Button buttonRemove;
    private Button buttonExplore;
    private Button buttonRestore;
    private Section section;
    private TLCErrorView view;

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
            } else if (source == buttonExplore)
            {
                doExplore();
            }
        }
    };

    // a listener reacting on selection in the table viewer
    protected ISelectionChangedListener fSelectionChangedListener = new ISelectionChangedListener() {
        public void selectionChanged(SelectionChangedEvent event)
        {
            Object source = event.getSource();
            if (source != null && source == tableViewer)
            {
                changeButtonEnablement();
            }
        }
    };

    public TraceExplorerComposite(Composite parent, String title, String description, FormToolkit toolkit,
            TLCErrorView errorView)
    {
        view = errorView;
        section = FormHelper.createSectionComposite(parent, title, description, toolkit, Section.DESCRIPTION
                | Section.TITLE_BAR | Section.TREE_NODE | Section.EXPANDED, null);
        /*
         * We want the section to take up the excess horizontal space so that it spans the entire
         * error view, but we dont want it to take up the excess vertical space because that
         * allows the sash form containing the trace and the variable viewer to expand into
         * the space left behind when the trace explorer table section is contracted.
         * 
         * This assumes the trace explorer table section is on top of this sash form.
         * I haven't tested to see if it will work when the trace explorer section is on the bottom.
         */
        GridData gd = new GridData(SWT.FILL, SWT.FILL, true, false);
        section.setLayoutData(gd);
        sectionInitialize(toolkit);
    }

    /**
     * Constructs the section content
     * 
     * This consists of setting the layout for the 
     * client area of the section, creating the table
     * for the section, creating the table viewer, and 
     * creating the buttons.
     * 
     * @param toolkit
     */
    protected void sectionInitialize(FormToolkit toolkit)
    {

        GridData gd;

        // create the composite
        Composite sectionArea = (Composite) section.getClient();
        sectionArea.setLayout(new GridLayout(2, false));

        // create the table
        Table table = createTable(sectionArea, toolkit);
        // The table grabs the entire space in the section
        gd = new GridData(GridData.FILL_BOTH);
        gd.grabExcessHorizontalSpace = true;
        gd.grabExcessVerticalSpace = true;
        // span for the buttons
        // there are currently 5 buttons, each occupying one
        // cell, so the table must span 5 vertical cells
        gd.verticalSpan = 5;
        table.setLayoutData(gd);

        // create the table viewer
        tableViewer = createTableViewer(table);

        // create buttons
        createButtons(sectionArea, toolkit);

        // setup the buttons
        changeButtonEnablement();
    }

    /**
     * This creates the table viewer. It should be called
     * within {@link TraceExplorerComposite#sectionInitialize(FormToolkit)}.
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

        tableViewer.setInput(new Vector());
        return tableViewer;
    }

    /**
     * Creates the table to be put into the tableviewer. It should be called
     * within {@link TraceExplorerComposite#sectionInitialize(FormToolkit)}.
     * 
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
    protected void createButtons(Composite sectionArea, FormToolkit toolkit)
    {
        GridData gd;

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

        // explore button
        buttonExplore = toolkit.createButton(sectionArea, "Explore", SWT.PUSH);
        buttonExplore.addSelectionListener(fSelectionListener);
        gd = new GridData();
        gd.verticalAlignment = SWT.TOP;
        gd.widthHint = 70;
        buttonExplore.setLayoutData(gd);

        // restore button
        buttonRestore = toolkit.createButton(sectionArea, "Restore", SWT.PUSH);
        buttonRestore.addSelectionListener(fSelectionListener);
        gd = new GridData();
        gd.verticalAlignment = SWT.TOP;
        gd.widthHint = 70;
        buttonRestore.setLayoutData(gd);

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

        saveInput();
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

            saveInput();

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
            tableViewer.refresh();
        }

        saveInput();
    }

    /**
     * Runs the trace explorer with the expressions
     * that are in the table.
     */
    private void doExplore()
    {
        /*
         * 
         */
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
        FormulaWizard wizard = new FormulaWizard(section.getText(), section.getDescription());
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
     * Saves the expressions in the table to the configuration
     * whose errors are currently loaded in the error view where this
     * composite appears.
     */
    private void saveInput()
    {
        try
        {
            if (view.getCurrentConfig() != null)
            {
                ILaunchConfigurationWorkingCopy configCopy;
                /*
                 * It is not clear if the current config
                 * of the view will always be a working copy or not.
                 * We perform this check just in case. 
                 */
                if (view.getCurrentConfig().isWorkingCopy())
                {
                    configCopy = (ILaunchConfigurationWorkingCopy) view.getCurrentConfig();
                } else
                {
                    configCopy = view.getCurrentConfig().getWorkingCopy();
                }
                configCopy.setAttribute(IModelConfigurationConstants.TRACE_EXPLORE_EXPRESSIONS, FormHelper
                        .getSerializedInput(tableViewer));
                ILaunchConfiguration savedConfig = configCopy.doSave();
                /*
                 * It is possible to have working copies of working copies, so
                 * we must make sure that the changes to the config are actually
                 * saved to the underlying file.
                 */
                while (savedConfig.isWorkingCopy())
                {
                    savedConfig = ((ILaunchConfigurationWorkingCopy) savedConfig).doSave();
                }
            }
        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error saving trace explorer expression.", e);
        }
    }

}
