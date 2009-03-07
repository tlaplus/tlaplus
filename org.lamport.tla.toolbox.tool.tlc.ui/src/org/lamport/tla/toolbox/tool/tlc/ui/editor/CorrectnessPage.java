package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.util.Vector;

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
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;

/**
 * Page for displaying what to check
 * @author Simon Zambrovski
 * @version $Id$
 */
public class CorrectnessPage extends BasicFormPage
{

    public static final String ID = "Correctness";
    
    private TableViewer invariantsTable;
    private TableViewer propertiesTable;

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
        
        Button deadlockButton = toolkit.createButton(body, "Check deadlock", SWT.CHECK);
        gd = new GridData();
        gd.horizontalSpan = 2;
        deadlockButton.setLayoutData(gd);
        
        // invariants
        TableSectionPart invariantsPart = new TableSectionPart(body, "Invariants", "Specify invariants to be checked in every state of the specification.", toolkit);
        managedForm.addPart(invariantsPart);
        
        
        // properties        
        TableSectionPart propertiesPart = new TableSectionPart(body, "Properties", "Specify properties to be checked.", toolkit);
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
        TableSectionPart initPart = new TableSectionPart(advancedArea, "Action constraints", "...", toolkit);
        managedForm.addPart(initPart);
        gd = (GridData) initPart.getTableViewer().getTable().getLayoutData();
        gd.widthHint = 100;
        // layout 
        gd = new GridData(GridData.FILL_HORIZONTAL);
        initPart.getSection().setLayoutData(gd);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.widthHint = 100;
        gd.verticalSpan = 2;
        initPart.getTableViewer().getTable().setLayoutData(gd);
        

        // actions part
        TableSectionPart actionsPart = new TableSectionPart(advancedArea, "Actions", "...", toolkit);
        managedForm.addPart(actionsPart);
        gd = (GridData) actionsPart.getTableViewer().getTable().getLayoutData();
        gd.widthHint = 100;
        // layout 
        gd = new GridData(GridData.FILL_HORIZONTAL);
        actionsPart.getSection().setLayoutData(gd);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.widthHint = 100;
        gd.verticalSpan = 2;
        actionsPart.getTableViewer().getTable().setLayoutData(gd);


        // action constraints
        TableSectionPart actionConstraintsPart = new TableSectionPart(advancedArea, "Init", "...", toolkit);
        managedForm.addPart(actionConstraintsPart);
        gd = (GridData) actionConstraintsPart.getTableViewer().getTable().getLayoutData();
        gd.widthHint = 100;
        // layout 
        gd = new GridData(GridData.FILL_HORIZONTAL);
        actionConstraintsPart.getSection().setLayoutData(gd);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.widthHint = 100;
        gd.verticalSpan = 2;
        actionConstraintsPart.getTableViewer().getTable().setLayoutData(gd);
        
        
        invariantsTable = invariantsPart.getTableViewer();
        propertiesTable = propertiesPart.getTableViewer();
        
        setData();
    }
    /**
     * 
     */
    private void setData()
    {
        invariantsTable.setInput(new Vector());
        propertiesTable.setInput(new Vector());
    }

    protected Layout getBodyLayout()
    {
        return FormHelper.createFormGridLayout(true, 2);
    } 
   
}
