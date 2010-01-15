package org.lamport.tla.toolbox.tool.tlc.ui.editor.part;

import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.runtime.Assert;
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
import org.lamport.tla.toolbox.tool.tlc.launch.TraceExplorerDelegate;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCState;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariable;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
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

    /*
     * These are used for writing init and next
     * for trace exploration.
     */
    private static final String TLA_AND = "/\\ ";
    private static final String TLA_OR = "\\/ ";
    private static final String EQ = "=";
    private static final String PRIME = "'";

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
        // edit on double-click on a formula
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

        try
        {
            // save the launch configuration
            ILaunchConfiguration modelConfig = saveInput();

            /*
             * Restore the original trace.
             * 
             * This is so that if the new run of the trace explorer completes successfully,
             * the error the originally produced the trace will appear in the error viewer
             * at the top of the error view.
             */
            doRestore();

            ILaunchConfigurationWorkingCopy workingCopy = modelConfig.getWorkingCopy();

            List trace = view.getTrace();

            // if the trace is empty, than do nothing
            // this will make the explore button appear to be a no-op
            // in the future, it should be disabled
            if (trace.size() > 0)
            {
                if (trace.get(0) instanceof TLCState)
                {
                    /*
                     * We store in the launch configuration object data from the trace
                     * in a form that hopefully makes it easy to parse the trace explorer
                     * expressions and generate the TE.tla and TE.cfg files that will
                     * be used to run TLC.
                     * 
                     * See comments in the methods of TraceExplorerDelegate for a description
                     * of how this data is used.
                     */
                    TLCState initialState = (TLCState) trace.get(0);
                    /*
                     *  Store a conjunction that gives the initial state of the trace.
                     *  For a spec with two variables, x and y, with an initial state in which
                     *  x = 4 and y = 6, we store:
                     *  
                     *  "/\ x = 4 /\ y = 6"
                     */
                    workingCopy.setAttribute(IModelConfigurationConstants.TRACE_INIT,
                            getConjunctionFromState(initialState));
                    /*
                     * Store a list of conjunctions that give the state transitions.
                     * For a spec with two variables, x and y, we do the following. If the third
                     * state in the trace has x = 2 and y = 1, and the fourth state has x = 3
                     * and y = 4, then the third element of the stored list will be the string:
                     * 
                     * "/\ x = 2 /\ y = 1 /\ x' = 3 /\ y' = 4"
                     */
                    workingCopy.setAttribute(IModelConfigurationConstants.TRACE_NEXT, getNextStateActionsFromTrace(view
                            .getTrace()));

                    /*
                     * We must store whether the final state is a stuttering state
                     * or is a "back to state". This affects what invariant or property will be used
                     * in order to get TLC to produce the same error trace with the new
                     * trace explorer variables.
                     */
                    TLCState finalState = (TLCState) trace.get(trace.size() - 1);
                    workingCopy.setAttribute(IModelConfigurationConstants.IS_TRACE_STUTTERING, finalState
                            .isStuttering());
                    workingCopy.setAttribute(IModelConfigurationConstants.IS_TRACE_BACK_TO_STATE, finalState
                            .isBackToState());
                    /*
                     * We store a conjunction describing the final state in the trace.
                     * This is used in the invariant or property that will be violated
                     * to produce the error trace with the trace explorer variables.
                     * If the final state is a stuttering state or a "back to state", then
                     * we store the second to last state.
                     */
                    if (finalState.isBackToState() || finalState.isStuttering())
                    {
                        workingCopy.setAttribute(IModelConfigurationConstants.TRACE_FINAL_STATE,
                                getConjunctionFromState((TLCState) trace.get(trace.size() - 2)));
                        if (finalState.isBackToState())
                        {
                            /*
                             * We store the state to which the trace returns. finalState.getStateNumber()
                             * gives the number of the state to which the trace returns. This information is
                             * used for creating the property which will be violated when the trace explorer
                             * is run for this trace.
                             */
                            workingCopy.setAttribute(IModelConfigurationConstants.TRACE_BACK_TO_STATE,
                                    getConjunctionFromState((TLCState) trace.get(finalState.getStateNumber() - 1)));

                            /*
                             * We store the number of states in the original trace. This is used after the run
                             * of TLC for the trace explorer. Note that this number does not count the "Back to State"
                             * as a state.
                             */
                            workingCopy.setAttribute(IModelConfigurationConstants.TRACE_NUM_STATES, trace.size() - 1);
                        }
                    } else
                    {
                        workingCopy.setAttribute(IModelConfigurationConstants.TRACE_FINAL_STATE,
                                getConjunctionFromState(finalState));
                    }

                    workingCopy.doSave().launch(TraceExplorerDelegate.MODE_TRACE_EXPLORE, null, true);

                    // set the model to have the trace with trace explorer expression shown
                    ModelHelper.setOriginalTraceShown(modelConfig, false);

                } else
                {
                    TLCUIActivator.logDebug("The first element of the trace is not a TLCState. This is a bug.");
                }

                /*
                 * The following will be used if I determine that it is necessary
                 * to have a seperate launch configuration file for the trace explorer.
                 * This may be necessary depending on the code that determines how output
                 * from TLC is displayed.
                 * 
                 * The following code copies the data from the model launch configuration
                 * to a trace explorer launch configuration file.
                 * 
                 * If this code is used, it should be moved above the preceeding else statement.
                 */

                // ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
                // ILaunchConfigurationType configType = launchManager
                // .getLaunchConfigurationType(TraceExplorerDelegate.LAUNCH_CONFIGURATION_TYPE);
                //
                // String traceConfigName = modelConfig.getName() + "__TE";
                //
                // // check if it has been created
                // ILaunchConfiguration[] configs;
                //
                // configs = launchManager.getLaunchConfigurations(configType);
                // for (int i = 0; i < configs.length; i++)
                // {
                // if (configs[i].getName().equals(traceConfigName))
                // {
                // configs[i].delete();
                // }
                // }
                //
                // workingCopy.doSave();
                //
                // ILaunchConfigurationWorkingCopy traceConfigCopy = modelConfig.copy(traceConfigName);
                //
                // traceConfigCopy.doSave().launch(TraceExplorerDelegate.MODE_TRACE_EXPLORE, null, true);
            }

        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error launching trace explorer.", e);
        }
    }

    /**
     * Restores the original trace produced by the last run of TLC for model checking (not trace exploration).
     */
    private void doRestore()
    {
        // get the data provider for the original model checking
        // run of TLC
        TLCModelLaunchDataProvider originalTraceProvider = TLCOutputSourceRegistry.getModelCheckSourceRegistry()
                .getProvider(view.getCurrentConfigFileHandle());

        // update the error view with this provider
        TLCErrorView.updateErrorView(originalTraceProvider, false);

        // set the model to have the original trace shown
        try
        {
            ModelHelper.setOriginalTraceShown(view.getCurrentConfigFileHandle(), true);
        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error setting original trace shown flag.", e);
        }
    }

    /**
     * If a formula in the table is selected, then enable the 
     * Remove and Edit buttons, else disable them.
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
     * 
     * @return a handle on the underlying configuration file, can return null
     */
    private ILaunchConfiguration saveInput()
    {
        try
        {
            if (view.getCurrentConfigFileHandle() != null)
            {
                /*
                 * Retrieve a working copy of the launch configuration whose errors
                 * are currently loaded in the error view.
                 * 
                 * If a model editor is open on the launch configuration, then the model
                 * editor already has a working copy open for the launch configuration. We
                 * don't want to open a second working copy because they could become out of
                 * synch. In that case if working copy A were saved and then working copy B were saved,
                 * the contents of working copy A that were saved originally would be overwritten by working
                 * copy B.
                 * 
                 * We can get the working copy from the model editor by calling the getConfig() method
                 * of ModelEditor. If there is not a model editor open on the launch configuration, then
                 * there should be no other working copies open on the the launch configuration returned
                 * by view.getCurrentConfigFileHandle() so a working copy can safely be used.
                 */
                ModelEditor modelEditor = ((ModelEditor) ModelHelper.getEditorWithModelOpened(view
                        .getCurrentConfigFileHandle()));

                ILaunchConfigurationWorkingCopy configCopy = null;

                if (modelEditor != null)
                {
                    configCopy = modelEditor.getConfig();
                } else
                {
                    // there is no editor open on the model
                    // obtain the working copy from the handle stored by the view
                    configCopy = view.getCurrentConfigFileHandle().getWorkingCopy();
                }

                configCopy.setAttribute(IModelConfigurationConstants.TRACE_EXPLORE_EXPRESSIONS, FormHelper
                        .getSerializedInput(tableViewer));
                ILaunchConfiguration savedConfig = configCopy.doSave();

                return savedConfig;
            }
        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error saving trace explorer expression.", e);
        }
        return null;
    }

    private static String getConjunctionFromState(TLCState state)
    {
        StringBuffer conjunction = new StringBuffer();
        TLCVariable[] variables = state.getVariables();
        for (int i = 0; i < variables.length; i++)
        {
            TLCVariable var = variables[i];
            conjunction.append(TLA_AND).append(var.getName()).append(EQ).append(var.getValue().toSimpleString());
        }

        return conjunction.toString();
    }

    /**
     * Returns a list of strings. Each String gives a next state
     * action corresponding to one step in the trace.
     * 
     * @param states
     * @return
     */
    private static List getNextStateActionsFromTrace(List states)
    {
        Vector actions = new Vector();

        Iterator it = states.iterator();
        TLCState currentState = null;
        TLCState nextState = null;
        if (it.hasNext())
        {
            Object first = it.next();
            Assert
                    .isTrue(first instanceof TLCState,
                            "The first element of the trace is not a TLCState. This is a bug.");
            currentState = (TLCState) first;
        } else
        {
            return actions;
        }
        while (it.hasNext())
        {
            Object next = it.next();
            Assert.isTrue(next instanceof TLCState, "An element of the trace is not a TLCState. It is an instance of "
                    + next.getClass().getCanonicalName() + ". This is a bug.");
            nextState = (TLCState) next;
            // must take into account stuttering states
            // and back to state states
            // need to test to see if this behaves properly
            if (nextState.isBackToState())
            {
                // next state is the state to which the trace returns
                nextState = (TLCState) states.get(nextState.getStateNumber() - 1);
            }
            if (nextState.isStuttering())
            {
                nextState = currentState;
            }
            StringBuffer actionConj = new StringBuffer();
            TLCVariable[] currentStateVariables = currentState.getVariables();
            TLCVariable[] nextStateVariables = nextState.getVariables();
            Assert.isTrue(currentStateVariables.length == nextStateVariables.length,
                    "The number of variables in one state is not the same as in another state of the trace.");

            for (int i = 0; i < currentStateVariables.length; i++)
            {
                TLCVariable var = currentStateVariables[i];
                actionConj.append(TLA_AND).append(var.getName()).append(EQ).append(var.getValue().toSimpleString());
            }

            for (int i = 0; i < nextStateVariables.length; i++)
            {
                TLCVariable var = nextStateVariables[i];
                actionConj.append(TLA_AND).append(var.getName()).append(PRIME).append(EQ).append(
                        var.getValue().toSimpleString());
            }

            actions.add(actionConj.toString());

            currentState = nextState;
        }

        return actions;
    }

}
