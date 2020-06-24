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

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Vector;
import java.util.stream.Collectors;

import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.resources.WorkspaceJob;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.ToolBarManager;
import org.eclipse.jface.dialogs.IDialogSettings;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.layout.GridDataFactory;
import org.eclipse.jface.util.LocalSelectionTransfer;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.dnd.DND;
import org.eclipse.swt.dnd.DragSource;
import org.eclipse.swt.dnd.DragSourceAdapter;
import org.eclipse.swt.dnd.DragSourceEvent;
import org.eclipse.swt.dnd.DropTarget;
import org.eclipse.swt.dnd.DropTargetAdapter;
import org.eclipse.swt.dnd.DropTargetEvent;
import org.eclipse.swt.dnd.Transfer;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.launch.TraceExplorerDelegate;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.dialog.ExtraModulesDialog;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.provider.FormulaContentProvider;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;
import org.lamport.tla.toolbox.tool.tlc.ui.wizard.FormulaWizard;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.RCPNameToFileIStream;

import tlc2.model.Formula;
import util.FilenameToStream;
import util.TLAConstants;

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
	private static final String EXPANDED_STATE = "EXPANDED_STATE";

	
    protected CheckboxTableViewer tableViewer;
    
    private Button buttonAdd;
    private Button buttonEdit;
    private Button buttonRemove;
    private Button buttonExplore;
    private Button buttonRestore;
    private Section section;
    private TLCErrorView view;

	private int m_tableIndexOfLastDragStart;
	
    // a listener reacting on button clicks
    // this calls the appropriate method when a user
    // clicks a button next to the table
    protected SelectionListener fSelectionListener = new SelectionAdapter() {
        public void widgetSelected(SelectionEvent e)
        {
            final Object source = e.getSource();
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
    protected ISelectionChangedListener m_formulaEnablementListener = (event) -> {
        final Object source = event.getSource();
        
		if ((source != null) && (source == tableViewer)) {
			changeButtonEnablement();
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
		// Initially, we want the section to be expanded for users to recognize the
		// error-trace exploration feature.  If a user collapses the section, it will
        // remain collapsed.
        final IDialogSettings dialogSettings = Activator.getDefault().getDialogSettings();
        if (dialogSettings.get(EXPANDED_STATE) != null) {
        	final boolean expand = dialogSettings.getBoolean(EXPANDED_STATE);
			section.setExpanded(expand);
        } else {
        	section.setExpanded(true);
        }
        section.addDisposeListener(new DisposeListener() {
			public void widgetDisposed(DisposeEvent e) {
				final IDialogSettings dialogSettings = Activator.getDefault().getDialogSettings();
		        dialogSettings.put(EXPANDED_STATE, section.isExpanded());
			}
        });
        
		final ToolBarManager toolBarManager = new ToolBarManager(SWT.FLAT);
		final ToolBar toolbar = toolBarManager.createControl(section);
		toolBarManager.add(new ExtraModulesActions());
		toolBarManager.update(true);
		section.setTextClient(toolbar);
    }

    private class ExtraModulesActions extends Action {

		public ExtraModulesActions() {
			super("Extend extra modules in trace expressions which are not extended by the actual spec.", TLCUIActivator
					.getImageDescriptor("platform:/plugin/org.eclipse.ui/icons/full/etool16/new_fastview.png"));
		}
    	
		@Override
		public void run() {
			final Spec currentSpec = ToolboxHandle.getCurrentSpec();
			if (currentSpec != null && view.getModel() != null) {
				// From the set of all modules remove those already included in the scope. The
				// remaining unused modules are the ones a user might potentially be additional
				// includes.
				final Set<String> availableModules = currentSpec.getModules().stream().map(m -> m.getModuleName())
						.collect(Collectors.toSet());
				final FilenameToStream resolver = currentSpec.getValidRootModule().getResolver();
				if (resolver instanceof RCPNameToFileIStream) {
					final RCPNameToFileIStream rcpResolver = (RCPNameToFileIStream) resolver;
					// Strip off ".tla" file extension.
					availableModules.addAll(rcpResolver.getAllModules().stream()
							.map(m -> m.replaceFirst((TLAConstants.Files.TLA_EXTENSION + "$"), ""))
							.collect(Collectors.toSet()));
				}
				final Set<String> includedModules = currentSpec.getValidRootModule().getModuleNames();
				
				final Set<String> unusedModules = availableModules.stream()
						.filter(m -> !includedModules.contains(m)).collect(Collectors.toSet());
				
				// Don't offer to extend  those modules which are already extended (implicitly).
				unusedModules.remove("Toolbox");
				unusedModules.remove("TLC");
				
				final ExtraModulesDialog extraModulesDialog = new ExtraModulesDialog(
						PlatformUI.getWorkbench().getDisplay().getActiveShell(), unusedModules,
						view.getModel().getTraceExplorerExtends());
				if (Window.OK == extraModulesDialog.open()) { 
					final Set<String> selectedModules = extraModulesDialog.getSelection();
					
					// Decouple I/O from UI thread.
			    	final Job job = new WorkspaceJob("Saving updated model...") {
						public IStatus runInWorkspace(final IProgressMonitor monitor) throws CoreException {
							view.getModel().setTraceExplorerExtends(selectedModules);
							view.getModel().save(monitor);
							return Status.OK_STATUS;
						}
					};
					job.setRule(ResourcesPlugin.getWorkspace().getRoot());
					job.setUser(true);
					job.schedule();
				}
			}
		}
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
        
        table.setToolTipText("Drag formulae to reorder.");

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
	protected CheckboxTableViewer createTableViewer(Table table) {
        // create
        final CheckboxTableViewer tableViewer = new CheckboxTableViewer(table);
        // represent formulas in the view
        tableViewer.setContentProvider(new FormulaContentProvider());
        // on changed selection change button enablement
        tableViewer.addSelectionChangedListener(m_formulaEnablementListener);
        // edit on double-click on a formula
		tableViewer.addDoubleClickListener((event) -> {
			doEdit();
		});

        // save the input when an element is checked or unchecked
		tableViewer.addCheckStateListener((event) -> {
			view.getModel().save(new NullProgressMonitor());
		});

        tableViewer.setInput(new Vector<Formula>());
        
        return tableViewer;
    }

    /**
     * Creates the table to be put into the tableviewer. It should be called
     * within {@link TraceExplorerComposite#sectionInitialize(FormToolkit)}.
     * 
     * @param sectionArea
     * @return
     */
	protected Table createTable(Composite sectionArea, FormToolkit toolkit) {
        final Table table = toolkit.createTable(sectionArea, SWT.MULTI | SWT.CHECK | SWT.V_SCROLL | SWT.H_SCROLL
                | SWT.FULL_SELECTION);
        
        table.setLinesVisible(false);
        table.setHeaderVisible(false);
        
        table.addKeyListener(new KeyListener() {
			@Override
			public void keyPressed(final KeyEvent ke) { }

			@Override
			public void keyReleased(final KeyEvent ke) {
				if ((ke.keyCode == SWT.BS) || (ke.keyCode == SWT.DEL)) {
					doRemove();
				}
			}
        });

		final Transfer[] types = new Transfer[] { LocalSelectionTransfer.getTransfer() };
		final DragSource source = new DragSource(table, DND.DROP_MOVE);
		source.setTransfer(types);
		source.addDragListener(new DragSourceAdapter() {
			@Override
			public void dragStart(final DragSourceEvent event) {
				final Table table = tableViewer.getTable();
				TableItem ti = (TableItem) table.getItem(new Point(event.x, event.y));

				if (ti != null) {
					m_tableIndexOfLastDragStart = table.indexOf(ti);
				} else {
					m_tableIndexOfLastDragStart = -1;
				}
			}
			
			@Override
			public void dragSetData(final DragSourceEvent event) {
				final IStructuredSelection selection = (IStructuredSelection) tableViewer.getSelection();

				LocalSelectionTransfer.getTransfer().setSelection(selection);
			}
		});

		// Create the drop target
		final DropTarget target = new DropTarget(table, DND.DROP_MOVE);
		target.setTransfer(types);
		target.addDropListener(new DropTargetAdapter() {
			public void dragOver(final DropTargetEvent event) {
		        event.feedback = DND.FEEDBACK_INSERT_BEFORE | DND.FEEDBACK_SCROLL;
				super.dragOver(event);
			}

			public void drop(final DropTargetEvent event) {
				final Object data = event.data;
				
				if (data instanceof IStructuredSelection) {
					final IStructuredSelection selection = (IStructuredSelection) data;
					if ((selection.size() > 0) && (selection.getFirstElement() instanceof Formula)) {
						final TableItem ti = (TableItem) event.item;
						final DropTarget target = (DropTarget) event.widget;
						final Table table = (Table) target.getControl();
						final int dropIndex = (ti == null) ? table.getItemCount() : table.indexOf(ti);
						@SuppressWarnings("unchecked")
						final Vector<Formula> model = (Vector<Formula>) tableViewer.getInput();
						final Iterator<?> it = selection.iterator();
						final int[] selectionIndices = new int[selection.size()];

						int counter = 0;
						while (it.hasNext()) {
							final Formula f = (Formula) it.next();

							selectionIndices[counter] = model.indexOf(f);
							counter++;
						}
						Arrays.sort(selectionIndices);
						
						final int dragDelta;
						if (m_tableIndexOfLastDragStart == -1) {
							dragDelta = dropIndex - selectionIndices[0];
						} else {
							dragDelta = dropIndex - m_tableIndexOfLastDragStart;
						}
						if (dragDelta == 0) {
							return;
						}
						
						final List<String> serializedOriginalModel = FormHelper.getSerializedInput(tableViewer);
						final int itemCount = serializedOriginalModel.size();
						final String[] movingItems = new String[selectionIndices.length];
						for (int i = 0; i < selectionIndices.length; i++) {
							movingItems[i] = serializedOriginalModel.get(selectionIndices[i]);
						}
						if (dragDelta > 0) {
							counter = selectionIndices.length - 1;
							for (int i = (itemCount - 1); i > -1; i--) {
								if (selectionIndices[counter] == i) {
									final String toMove = movingItems[counter];
									// i tried all manner of working solely with the selectionIndices but could get no
									//		obvious global solution more moving multiple contiguous and moving multiple
									//		disjoint items - so i ended up with this indexOf lookup
									final int adjustedMoveIndex = serializedOriginalModel.indexOf(toMove);
									int newIndex = i + dragDelta;
									
									if (newIndex > itemCount) {
										newIndex = itemCount;
									}
									
									serializedOriginalModel.add(newIndex, toMove);
									serializedOriginalModel.remove(adjustedMoveIndex);

									counter--;
									if (counter < 0) {
										break;
									}
								}
							}
						} else {
							counter = 0;
							for (int i = 0; i < itemCount; i++) {
								if (selectionIndices[counter] == i) {
									final String toMove = movingItems[counter];
									// i tried all manner of working solely with the selectionIndices but could get no
									//		obvious global solution more moving multiple contiguous and moving multiple
									//		disjoint items - so i ended up with this indexOf lookup
									final int adjustedMoveIndex = serializedOriginalModel.indexOf(toMove);
									int newIndex = i + dragDelta;
									
									if (newIndex < 0) {
										newIndex = 0;
									}
									
									serializedOriginalModel.remove(adjustedMoveIndex);
									serializedOriginalModel.add(newIndex, toMove);

									counter++;
									if (counter == selectionIndices.length) {
										break;
									}
								}
							}
						}

						tableViewer.setInput(new Vector<Formula>());
						FormHelper.setSerializedInput(tableViewer, serializedOriginalModel);

						changeButtonEnablement();
						
						saveModel();
					}
				}
			}
		});
        
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
        final GridData gd = new GridData();
        gd.verticalAlignment = SWT.TOP;
        gd.horizontalAlignment = SWT.FILL;

        // add button
        buttonAdd = toolkit.createButton(sectionArea, "Add", SWT.PUSH);
        buttonAdd.addSelectionListener(fSelectionListener);
        buttonAdd.setLayoutData(GridDataFactory.copyData(gd));

        // edit button
        buttonEdit = toolkit.createButton(sectionArea, "Edit", SWT.PUSH);
        buttonEdit.addSelectionListener(fSelectionListener);
        buttonEdit.setLayoutData(GridDataFactory.copyData(gd));

        // remove button
        buttonRemove = toolkit.createButton(sectionArea, "Remove", SWT.PUSH);
        buttonRemove.addSelectionListener(fSelectionListener);
        buttonRemove.setLayoutData(GridDataFactory.copyData(gd));

        // explore button
        buttonExplore = toolkit.createButton(sectionArea, "Explore", SWT.PUSH);
        buttonExplore.addSelectionListener(fSelectionListener);
        buttonExplore.setLayoutData(GridDataFactory.copyData(gd));

        // restore button
        buttonRestore = toolkit.createButton(sectionArea, "Restore", SWT.PUSH);
        buttonRestore.addSelectionListener(fSelectionListener);
        buttonRestore.setLayoutData(GridDataFactory.copyData(gd));
        buttonRestore.setEnabled(false);
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
     * @return the <code>Section</code> instance for this composite.
     */
    public Section getSection() {
    	return section;
    }

    /**
     * Remove the selected formulas
     */
    protected void doRemove()
    {
        final IStructuredSelection selection = (IStructuredSelection) tableViewer.getSelection();
        final Vector<?> input = (Vector<?>)tableViewer.getInput();
        
        input.removeAll(selection.toList());
        tableViewer.setInput(input);

        changeButtonEnablement();

        saveModel();
    }

    /**
     * Add a formula to the list
     */
    protected void doAdd()
    {
        Formula formula = doEditFormula(null);

        // add a formula
		if (formula != null) {
            @SuppressWarnings("unchecked")
			Vector<Formula> input = ((Vector<Formula>) tableViewer.getInput());
            input.add(formula);
            tableViewer.setInput(input);
			if (tableViewer instanceof CheckboxTableViewer) {
                ((CheckboxTableViewer) tableViewer).setChecked(formula, true);
            }

            changeButtonEnablement();

            saveModel();
        }
    }

    /**
     * Edit selected formula 
     */
	protected void doEdit() {
        final IStructuredSelection selection = (IStructuredSelection) tableViewer.getSelection();
        final Formula formula;
        
        if (selection.size() == 1) {
        	formula = (Formula) selection.getFirstElement();
        } else {
        	formula = (Formula) tableViewer.getElementAt(0);
        }
        
        final Formula editedFormula = doEditFormula(formula);
		if (editedFormula != null) {
			formula.setFormula(editedFormula.getFormula());
			if (tableViewer instanceof CheckboxTableViewer) {
				((CheckboxTableViewer) tableViewer).setChecked(formula, true);
            }
            tableViewer.refresh();
        }

        saveModel();
    }
    
    private void saveModel() {
        view.getModel().setTraceExplorerExpression(FormHelper.getSerializedInput(tableViewer));
        
    	final Job job = new WorkspaceJob("Saving updated model...") {
			public IStatus runInWorkspace(final IProgressMonitor monitor) throws CoreException {
				view.getModel().save(monitor);
				return Status.OK_STATUS;
			}
		};
		job.setRule(ResourcesPlugin.getWorkspace().getRoot());
		job.setUser(true);
		job.schedule();
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

        // If we don't do this, the selection of formulas will not be carried to the execution
        view.getModel().setTraceExplorerExpression(FormHelper.getSerializedInput(tableViewer));
        
        // Save model without validating.
        // Validating would erase MC.out, which we dont want
        // the trace explorer to do.
        // This could erase a trace that was produced
        // after a three week run of TLC.
        modelEditor.doSaveWithoutValidating((new NullProgressMonitor()));

        // save the launch configuration
        // if the trace is empty, then do nothing
		if (!view.getTrace().isTraceEmpty()) {
            // TraceExplorerHelper.serializeTrace(modelConfig);
        	
        	// Wrap the launch in a WorkspaceJob to guarantee that the
        	// operation is executed atomically from the workspace perspective.
        	// If the runnable would be omitted, the launch can become interleaved with
        	// workspace (autobuild) jobs triggered by IResourceChange events.
        	// The Toolbox's IResourceChangeListeners reacting to resource change events
        	// run the SANY parser and SANY does not support concurrent execution.
        	
        	final Job job = new WorkspaceJob("Exploring the trace...") {
				public IStatus runInWorkspace(final IProgressMonitor monitor) throws CoreException {
					view.getModel().save(monitor).launch(TraceExplorerDelegate.MODE_TRACE_EXPLORE, monitor, true);
					return Status.OK_STATUS;
				}
			};
			job.setRule(ResourcesPlugin.getWorkspace().getRoot());
			job.setUser(true);
			job.schedule();
			
			if (Boolean.getBoolean(TLCErrorView.class.getName() + ".noRestore")) {
				return;
			}
			
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
        buttonRemove.setEnabled(!((IStructuredSelection)tableViewer.getSelection()).isEmpty());

        if (Boolean.getBoolean(TLCErrorView.class.getName() + ".noRestore")) {
			return;
		}
        
        buttonRestore.setEnabled(false);
    }

    /**
	 * If a formula in the table is selected, then enable the Remove and Edit
	 * buttons, else disable the Remove button, and the Edit button iff there are 0
	 * or many formulas in the table.
	 */
	public void changeButtonEnablement() {
    	if (tableViewer == null) {
    		return;
    	}
    	
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
            buttonEdit.setEnabled((selection.size() == 1) || (tableViewer.getTable().getItemCount() == 1));
        }
        
        if (buttonExplore != null)
        {
			if (Boolean.getBoolean(TLCErrorView.class.getName() + ".noRestore")) {
				buttonExplore.setEnabled(tableViewer.getCheckedElements().length> 0);
			} else {
	            buttonExplore.setEnabled((view.getTrace() != null) && !view.getTrace().isTraceEmpty()
	                    && (tableViewer.getCheckedElements().length> 0));
			}
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
		FormulaWizard wizard = new FormulaWizard(section.getText(),
				"Enter an expression to be evaluated at each state of the trace.",
				String.format(
						"The expression may be named and may include the %s and %s operators (click question mark below for details).",
						TLAConstants.TraceExplore.TRACE, TLAConstants.TraceExplore.POSITION),
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
