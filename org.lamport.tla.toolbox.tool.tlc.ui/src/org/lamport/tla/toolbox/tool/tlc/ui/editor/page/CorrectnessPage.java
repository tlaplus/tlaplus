package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.util.List;
import java.util.Vector;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Layout;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.EmptyPart;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.TableSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;

/**
 * Page for displaying what to check
 * @author Simon Zambrovski
 * @version $Id$
 * @deprecated
 */
public class CorrectnessPage extends BasicFormPage
{

    public static final String ID = "Correctness";
    
    private TableViewer invariantsTable;
    private TableViewer propertiesTable;
    private TableViewer initTable;
    private TableViewer actionsTable;
    private TableViewer actionConstraintTable;

    private Button checkDeadlockButton;

    public CorrectnessPage(FormEditor editor)
    {
        super(editor, CorrectnessPage.ID, "Correctness");
        this.helpId = IHelpConstants.CORRECTNESS_MODEL_PAGE;
        this.imagePath = "icons/full/correctness_obj.gif";
    }

    protected void createBodyContent(IManagedForm managedForm)
    {
        GridData gd;
        Composite body = managedForm.getForm().getBody();
        FormToolkit toolkit = managedForm.getToolkit();
        
        checkDeadlockButton = toolkit.createButton(body, "Check deadlock", SWT.CHECK);
        gd = new GridData();
        gd.horizontalSpan = 2;
        checkDeadlockButton.setLayoutData(gd);

        // deadlock part        
        EmptyPart deadlockPart = new EmptyPart();
        deadlockPart.addControl(checkDeadlockButton);
        managedForm.addPart(deadlockPart);
        
        //listener
        DirtyMarkingListener listener = new DirtyMarkingListener(deadlockPart, true);
        checkDeadlockButton.addSelectionListener(listener);
        
        // invariants
        TableSectionPart invariantsPart = new TableSectionPart(body, "Invariants", "Specify invariants to be checked in every state of the specification.", toolkit, this);
        managedForm.addPart(invariantsPart);
        
        
        // properties        
        TableSectionPart propertiesPart = new TableSectionPart(body, "Properties", "Specify properties to be checked.", toolkit, this);
        managedForm.addPart(propertiesPart);



        // advanced tab
        Section section = FormHelper.createSectionComposite(body, "Advanced", "", toolkit, Section.TITLE_BAR
                | Section.TWISTIE | Section.COMPACT, getExpansionListener());
        // only grab horizontal space
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 2;
        section.setLayoutData(gd);

        Composite advancedArea = (Composite) section.getClient();
        GridLayout layout = new GridLayout();
        layout.numColumns = 3;
        advancedArea.setLayout(layout);

        // init part
        TableSectionPart initPart = new TableSectionPart(advancedArea, "Init", "...", toolkit, this);
        managedForm.addPart(initPart);
        gd = (GridData) initPart.getTableViewer().getTable().getLayoutData();
        gd.widthHint = 100;
        // layout 
        gd = new GridData(GridData.FILL_HORIZONTAL);
        initPart.getSection().setLayoutData(gd);
        gd = new GridData(GridData.FILL_BOTH);
        gd.widthHint = 100;
        gd.verticalSpan = 3;
        initPart.getTableViewer().getTable().setLayoutData(gd);
        

        // actions part
        TableSectionPart actionsPart = new TableSectionPart(advancedArea, "Actions", "...", toolkit, this);
        managedForm.addPart(actionsPart);
        gd = (GridData) actionsPart.getTableViewer().getTable().getLayoutData();
        gd.widthHint = 100;
        // layout 
        gd = new GridData(GridData.FILL_HORIZONTAL);
        actionsPart.getSection().setLayoutData(gd);
        gd = new GridData(GridData.FILL_BOTH);
        gd.widthHint = 100;
        gd.verticalSpan = 3;
        actionsPart.getTableViewer().getTable().setLayoutData(gd);


        // action constraints
        TableSectionPart actionConstraintsPart = new TableSectionPart(advancedArea, "Action constraints", "...", toolkit, this);
        managedForm.addPart(actionConstraintsPart);
        gd = (GridData) actionConstraintsPart.getTableViewer().getTable().getLayoutData();
        gd.widthHint = 100;
        // layout 
        gd = new GridData(GridData.FILL_HORIZONTAL);
        actionConstraintsPart.getSection().setLayoutData(gd);
        gd = new GridData(GridData.FILL_BOTH);
        gd.widthHint = 100;
        gd.verticalSpan = 3;
        actionConstraintsPart.getTableViewer().getTable().setLayoutData(gd);
        
        
        invariantsTable = invariantsPart.getTableViewer();
        propertiesTable = propertiesPart.getTableViewer();
        initTable = initPart.getTableViewer();
        actionsTable = actionsPart.getTableViewer();
        actionConstraintTable = actionConstraintsPart.getTableViewer();

        dirtyPartListeners.add(listener);
    }

    
    /**
     * load data from the model
     */
    protected void loadData() throws CoreException
    {
        // check deadlock
        boolean checkDeadlock = getConfig().getAttribute(MODEL_CORRECTNESS_CHECK_DEADLOCK, MODEL_CORRECTNESS_CHECK_DEADLOCK_DEFAULT);
        this.checkDeadlockButton.setSelection(checkDeadlock);
        
        // invariants
        List serializedList= getConfig().getAttribute(MODEL_CORRECTNESS_INVARIANTS, new Vector());
        FormHelper.setSerializedInput(invariantsTable, serializedList);

        // properties
        serializedList = getConfig().getAttribute(MODEL_CORRECTNESS_PROPERTIES, new Vector());
        FormHelper.setSerializedInput(propertiesTable, serializedList);

        // init
        serializedList = getConfig().getAttribute(MODEL_CORRECTNESS_INIT, new Vector());
        FormHelper.setSerializedInput(initTable, serializedList);

        // actions
        serializedList = getConfig().getAttribute(MODEL_CORRECTNESS_ACTIONS, new Vector());
        FormHelper.setSerializedInput(actionsTable, serializedList);

        // actions constraints
        serializedList = getConfig().getAttribute(MODEL_PARAMETER_ACTION_CONSTRAINT, new Vector());
        FormHelper.setSerializedInput(actionConstraintTable, serializedList);
    }

    /**
     * Commit data to the model
     */
    public void commit(boolean onSave)
    {

        // check deadlock 
        boolean checkDeadlock = this.checkDeadlockButton.getSelection();
        getConfig().setAttribute(MODEL_CORRECTNESS_CHECK_DEADLOCK, checkDeadlock);
        
        // invariants
        List serializedList = FormHelper.getSerializedInput(invariantsTable);
        getConfig().setAttribute(MODEL_CORRECTNESS_INVARIANTS, serializedList);

        // properties
        serializedList = FormHelper.getSerializedInput(propertiesTable);
        getConfig().setAttribute(MODEL_CORRECTNESS_PROPERTIES, serializedList);

        // init
        serializedList = FormHelper.getSerializedInput(initTable);
        getConfig().setAttribute(MODEL_CORRECTNESS_INIT, serializedList);

        // actions
        serializedList = FormHelper.getSerializedInput(actionsTable);
        getConfig().setAttribute(MODEL_CORRECTNESS_ACTIONS, serializedList);

        // action constraints
        serializedList = FormHelper.getSerializedInput(actionConstraintTable);
        getConfig().setAttribute(MODEL_PARAMETER_ACTION_CONSTRAINT, serializedList);
        
        super.commit(onSave);
    } 

    
    protected Layout getBodyLayout()
    {
        return FormHelper.createFormGridLayout(true, 2);
    }

   
}
