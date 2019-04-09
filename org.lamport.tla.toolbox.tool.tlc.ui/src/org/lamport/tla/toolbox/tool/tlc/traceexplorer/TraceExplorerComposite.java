/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Dan Rickett - initial API and implementation
 ******************************************************************************/

package org.lamport.tla.toolbox.tool.tlc.traceexplorer;

import java.util.Vector;

import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.resources.WorkspaceJob;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
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
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.launch.TraceExplorerDelegate;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.tool.tlc.model.TraceExpressionModelWriter;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.provider.FormulaContentProvider;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;
import org.lamport.tla.toolbox.tool.tlc.ui.wizard.FormulaWizard;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

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
 * {@link TraceExplorerComposite#sectionInitialize(FormToolkit)} is called within the constructor
 * to setup the widgets for the section (i.e. table, table viewer, buttons).
 * 
 * {@link TraceExplorerComposite#doAdd()} is called when the user clicks the add button.
 * 
 * {@link TraceExplorerComposite#doEdit()} is called when the user clicks the edit button.
 * 
 * {@link TraceExplorerComposite#doRemove()} is called when the user clicks the remove button.
 * 
 * {@link TraceExplorerComposite#doExplore()} is called when the user clicks the explore button.
 * 
 * {@link TraceExplorerComposite#doRestore()} is called when the user clicks the explore button.
 */
public class TraceExplorerComposite
{
    protected CheckboxTableViewer tableViewer;
    private Button buttonAdd;
    private Button buttonEdit;
    private Button buttonRemove;
    private Button buttonExplore;
    private Button buttonRestore;
    private Section section;
    private TLCErrorView view;

    // a listener reacting on button clicks
    // this calls the appropriate method when a user
    // clicks a button next to the table
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
            } else if (source == buttonRestore)
            {
                doRestore();
            }
        }
    };

    // a listener reacting on selection in the table viewer
    // this calls the method that changes button enablement
    // depending on whether a formula is selected or not
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
        // initially, we don't want the section to be expanded
        // so that the user has more room to look at the trace
        section.setExpanded(false);
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
    protected CheckboxTableViewer createTableViewer(Table table)
    {
        // create
        CheckboxTableViewer tableViewer = new CheckboxTableViewer(table);
        // represent formulas in the view
        tableViewer.setContentProvider(new FormulaContentProvider());
        // on changed selection change button enablement
        tableViewer.addSelectionChangedListener(fSelectionChangedListener);
        // edit on double-click on a formula
        tableViewer.addDoubleClickListener(new IDoubleClickListener() {
            public void doubleClick(DoubleClickEvent event)
            {
                doEdit();
            }
        });

        // save the input when an element is checked or unchecked
        tableViewer.addCheckStateListener(new ICheckStateListener() {

            public void checkStateChanged(CheckStateChangedEvent event)
            {
                view.getModel().save(new NullProgressMonitor());
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
     * Creates buttons. Currently, this creates the following buttons:
     * 
     * Add
     * Edit
     * Remove
     * Explore
     * Restore
     * 
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

        changeButtonEnablement();

        view.getModel().setTraceExplorerExpression(FormHelper.getSerializedInput(tableViewer));
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
            @SuppressWarnings("unchecked")
			Vector<Formula> input = ((Vector<Formula>) tableViewer.getInput());
            input.add(formula);
            tableViewer.setInput(input);
            if (tableViewer instanceof CheckboxTableViewer)
            {
                ((CheckboxTableViewer) tableViewer).setChecked(formula, true);
            }

            changeButtonEnablement();

            view.getModel().setTraceExplorerExpression(FormHelper.getSerializedInput(tableViewer));
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

        changeButtonEnablement();

        view.getModel().setTraceExplorerExpression(FormHelper.getSerializedInput(tableViewer));
    }

    /**
     * Runs the trace explorer with the expressions
     * that are in the table.
     */
    private void doExplore()
    {
        /*
         * Check for module TE in spec.
         * Cannot run trace explorer if the spec contains a module named TE.
         */
        String rootModuleFileName = ToolboxHandle.getRootModule().getName();
        if (ModelHelper.containsTraceExplorerModuleConflict(rootModuleFileName))
        {
            MessageDialog.openError(view.getSite().getShell(), "Illegal module name",
                    "Trace exploration is not allowed for a spec that contains a module named "
                            + ModelHelper.TE_MODEL_NAME + ".");
            return;
        }

        /*
         * Check for validation errors.
         * 
         * If there is a validation error in the model, switch to a page
         * with an error, display a message to the user indicating that
         * the trace explorer cannot be run with a validation error, and
         * do not run the trace explorer.
         * 
         * If a model editor is not open on this model, then it is not
         * currently possible to check for validation errors, so the
         * trace explorer cannot be run.
         */
        final ModelEditor modelEditor = view.getModel().getAdapter(ModelEditor.class);
        if (modelEditor == null)
        {
            // the model editor must be open to run the trace explorer
            // in order to detect validation errors
            // the model editor is null, so show a message to the user
            // and do not run the trace explorer
            MessageDialog
                    .openError(
                            view.getSite().getShell(),
                            "Trace exploration not allowed",
                            "There is no model editor open on this model. The trace explorer cannot be run without opening the model editor on this model.");

            return;
        } else if (!modelEditor.isComplete())
        {
            // validation error
            MessageDialog.openError(view.getSite().getShell(), "Trace exploration not allowed",
                    "The model contains errors, which should be corrected before running the trace explorer.");

            // do not run trace explorer
            return;
        }

        // Save model without validating.
        // Validating would erase MC.out, which we dont want
        // the trace explorer to do.
        // This could erase a trace that was produced
        // after a three week run of TLC.
        modelEditor.doSaveWithoutValidating((new NullProgressMonitor()));

        // save the launch configuration
        // if the trace is empty, then do nothing
        if (!view.getTrace().isTraceEmpty())
        {
            // TraceExplorerHelper.serializeTrace(modelConfig);
        	
        	// Wrap the launch in a WorkspaceJob to guarantee that the
        	// operation is executed atomically from the workspace perspective.
        	// If the runnable would be omitted, the launch can become interleaved with
        	// workspace (autobuild) jobs triggered by IResourceChange events.
        	// The Toolbox's IResourceChangeListeners reacting to resource change events
        	// run the SANY parser and SANY does not support concurrent execution.
        	
        	final Job job = new WorkspaceJob("Exploring the trace...") {
				public IStatus runInWorkspace(IProgressMonitor monitor) throws CoreException {
					view.getModel().save(monitor).launch(TraceExplorerDelegate.MODE_TRACE_EXPLORE, monitor, true);
					return Status.OK_STATUS;
				}
			};
			job.setRule(ResourcesPlugin.getWorkspace().getRoot());
			job.setUser(true);
			job.schedule();
			
	        tableViewer.getTable().setEnabled(false);
	        
	        buttonExplore.setEnabled(false);
	        buttonAdd.setEnabled(false);
	        buttonEdit.setEnabled(false);
	        buttonRemove.setEnabled(false);
	        
	        buttonRestore.setEnabled(true);
        }
    }

    /**
     * Restores the original trace produced by the last run of TLC for model checking (not trace exploration).
     */
    private void doRestore()
    {
        // set the model to have the original trace shown
    	view.setOriginalTraceShown(true);

        // update the error view with this provider
        view.updateErrorView();
        
        tableViewer.getTable().setEnabled(true);
        
        buttonExplore.setEnabled(true);
        buttonAdd.setEnabled(true);
        buttonEdit.setEnabled(true);
        buttonRemove.setEnabled(true);
        
        buttonRestore.setEnabled(false);
    }

    /**
     * If a formula in the table is selected, then enable the 
     * Remove and Edit buttons, else disable them.
     */
    protected void changeButtonEnablement()
    {
        IStructuredSelection selection = (IStructuredSelection) tableViewer.getSelection();
        if (!tableViewer.getTable().isEnabled()) {
        	return;
        }

        if (buttonRemove != null)
        {
            buttonRemove.setEnabled(!selection.isEmpty());
        }
        if (buttonEdit != null)
        {
            buttonEdit.setEnabled(selection.size() == 1);
        }
        if (buttonExplore != null)
        {
            buttonExplore.setEnabled(view.getTrace() != null && !view.getTrace().isTraceEmpty()
                    && tableViewer.getCheckedElements().length > 0);
        }
    }

    /**
     * Sets the explore button enablement status to isTrace.
     * @param isTrace
     */
    public void changeExploreEnablement(boolean isTrace)
    {
        buttonExplore.setEnabled(isTrace);
    }

    /**
     * Opens a dialog for formula processing and returns the edited formula  
     * @param formula initial formula, can be <code>null</code>
     * @return result of editing or <code>null</code>, if editing canceled
     */
    protected Formula doEditFormula(Formula formula)
    {
        // Create the wizard
		FormulaWizard wizard = new FormulaWizard(section.getText(),
				"Enter an expression to be evaluated at each state of the trace.",
				String.format(
						"The expression may be named and may include the %s and %s operators (click question mark below for details).",
						TraceExpressionModelWriter.TRACE, TraceExpressionModelWriter.POSITION),
				"ErrorTraceExplorerExpression");
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
}
