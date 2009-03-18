package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.util.Vector;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Layout;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.SectionPart;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;

/**
 * Page for displaying parameters
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParametersPage extends BasicFormPage
{

    public static final String ID = "Parameters";
    private SourceViewer constraintSource;
    private CheckboxTableViewer definitionsTable;
    private CheckboxTableViewer newDefinitionsTable;
    private CheckboxTableViewer symmetryTable;
    private CheckboxTableViewer constantTable;

    public ParametersPage(FormEditor editor)
    {
        super(editor, ParametersPage.ID, "Parameters");
        this.helpId = IHelpConstants.PARAMETERS_MODEL_PAGE;
        this.imagePath = "icons/full/args_obj.gif";
    }

    protected void createBodyContent(IManagedForm managedForm)
    {
        GridData gd;
        Composite body = managedForm.getForm().getBody();
        FormToolkit toolkit = managedForm.getToolkit();

        // Constants
        TableSectionPart constantsPart = new TableSectionPart(body, "Constants instantiation",
                "Specify the values of the model constants.", toolkit);
        managedForm.addPart(constantsPart);

        // advanced tab
        Section section = FormHelper.createSectionComposite(body, "Advanced", "", toolkit, Section.TITLE_BAR
                | Section.TWISTIE | Section.COMPACT, getExpansionListener());
        // only grab horizontal space
        gd = new GridData(GridData.FILL_HORIZONTAL);
        section.setLayoutData(gd);

        Composite advancedArea = (Composite) section.getClient();
        GridLayout layout = new GridLayout();
        layout.numColumns = 3;
        advancedArea.setLayout(layout);

        // definition overwrite
        TableSectionPart definitionsPart = new TableSectionPart(advancedArea, "Definition Override", "...", toolkit);
        managedForm.addPart(definitionsPart);
        // layout 
        gd = new GridData(GridData.FILL_HORIZONTAL);
        definitionsPart.getSection().setLayoutData(gd);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.widthHint = 100;
        gd.verticalSpan = 3;
        definitionsPart.getTableViewer().getTable().setLayoutData(gd);

        // new definitions
        TableSectionPart newDefinitionPart = new TableSectionPart(advancedArea, "New Definitions", "...", toolkit);
        managedForm.addPart(newDefinitionPart);
        // layout
        gd = new GridData(GridData.FILL_HORIZONTAL);
        newDefinitionPart.getSection().setLayoutData(gd);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.widthHint = 100;
        gd.verticalSpan = 3;
        newDefinitionPart.getTableViewer().getTable().setLayoutData(gd);

        // symmetry
        TableSectionPart symmetryPart = new TableSectionPart(advancedArea, "Symmetry", "...", toolkit);
        managedForm.addPart(symmetryPart);
        // layout
        gd = new GridData(GridData.FILL_HORIZONTAL);
        symmetryPart.getSection().setLayoutData(gd);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.widthHint = 100;
        gd.verticalSpan = 3;
        symmetryPart.getTableViewer().getTable().setLayoutData(gd);

        // constraint
        Section constraintSection = FormHelper.createSectionComposite(advancedArea, "Constraint", "...", toolkit,
                Section.DESCRIPTION | Section.TITLE_BAR | Section.TWISTIE | Section.COMPACT, getExpansionListener());
        SectionPart constraintPart = new SectionPart(constraintSection);
        managedForm.addPart(constraintPart);
        DirtyMarkingListener constraintListener = new DirtyMarkingListener(constraintPart, true);
        
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 3;
        constraintSection.setLayoutData(gd);

        Composite constraintArea = (Composite) constraintSection.getClient();
        constraintSource = FormHelper.createSourceViewer(toolkit, constraintArea, SWT.V_SCROLL);
        // layout of the source viewer
        TableWrapData twd = new TableWrapData(TableWrapData.FILL);
        twd.heightHint = 60;
        twd.grabHorizontal = true;
        constraintSource.getTextWidget().setLayoutData(twd);
        constraintSource.addTextListener(constraintListener);

        definitionsTable = definitionsPart.getTableViewer();
        newDefinitionsTable = newDefinitionPart.getTableViewer();
        symmetryTable = symmetryPart.getTableViewer();
        constantTable = constantsPart.getTableViewer();
        
        ignoringListeners.add(constraintListener);
    }

    protected void loadData() throws CoreException
    {
        IDocument constraintDocument = new Document();
        constraintSource.setDocument(constraintDocument);
        
        constantTable.setInput(new Vector());
        symmetryTable.setInput(new Vector());
        definitionsTable.setInput(new Vector());
        newDefinitionsTable.setInput(new Vector());
        
    }
    
    
    protected Layout getBodyLayout()
    {
        return FormHelper.createFormGridLayout(false, 1);
    }
    
}
