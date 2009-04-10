package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.util.List;
import java.util.Vector;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.TableViewer;
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
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ConstantSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.TableSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;

import tla2sany.semantic.ModuleNode;

/**
 * Page for displaying parameters
 * @author Simon Zambrovski
 * @version $Id$
 * @deprecated
 */
public class ParametersPage extends BasicFormPage
{

    public static final String ID = "Parameters";
    private SourceViewer constraintSource;
    private TableViewer definitionsTable;
    private TableViewer newDefinitionsTable;
    private TableViewer symmetryTable;
    private TableViewer constantTable;
    

    public ParametersPage(FormEditor editor)
    {
        super(editor, ParametersPage.ID, "Parameters");
        this.helpId = IHelpConstants.PARAMETERS_MODEL_PAGE;
        this.imagePath = "icons/full/args_obj.gif";
    }

    protected void loadData() throws CoreException
    {
        // constraint
        String constraint = getConfig().getAttribute(MODEL_PARAMETER_CONSTRAINT, EMPTY_STRING);
        constraintSource.setDocument(new Document(constraint));
        
        // constants from the model
        List savedConstants = getConfig().getAttribute(MODEL_PARAMETER_CONSTANTS, new Vector());

        // get the root module
        ModuleNode moduleNode = ToolboxHandle.getSpecObj().getExternalModuleTable().getRootModule();
        // get the list of constants
        List constants = ModelHelper.createConstantsList(moduleNode);
        

        // TODO check if new constants exist...
        
        FormHelper.setSerializedInput(constantTable, savedConstants);
        

        
        
        // symmetry
        List symmetry = getConfig().getAttribute(MODEL_PARAMETER_SYMMETRY, new Vector());
        FormHelper.setSerializedInput(symmetryTable, symmetry);
        
        // definition overrides
        List definitions = getConfig().getAttribute(MODEL_PARAMETER_DEFINITIONS, new Vector());
        FormHelper.setSerializedInput(definitionsTable, definitions);
        
        // new definitions
        List newDefinitions = getConfig().getAttribute(MODEL_PARAMETER_NEW_DEFINITIONS, new Vector());
        FormHelper.setSerializedInput(newDefinitionsTable, newDefinitions);
    }
    
    public void commit(boolean onSave)
    {
        List constants = FormHelper.getSerializedInput(constantTable);
        getConfig().setAttribute(MODEL_PARAMETER_CONSTANTS, constants);

        List symmetry = FormHelper.getSerializedInput(symmetryTable);
        getConfig().setAttribute(MODEL_PARAMETER_SYMMETRY, symmetry);

        List definitions = FormHelper.getSerializedInput(definitionsTable);
        getConfig().setAttribute(MODEL_PARAMETER_DEFINITIONS, definitions);

        List newDefinitions = FormHelper.getSerializedInput(newDefinitionsTable);
        getConfig().setAttribute(MODEL_PARAMETER_NEW_DEFINITIONS, newDefinitions);

        String constraintFormula = constraintSource.getDocument().get();
        getConfig().setAttribute(MODEL_PARAMETER_CONSTRAINT, constraintFormula);
        
        super.commit(onSave);
    }

    
    protected void createBodyContent(IManagedForm managedForm)
    {
        GridData gd;
        Composite body = managedForm.getForm().getBody();
        FormToolkit toolkit = managedForm.getToolkit();

        // Constants
        ConstantSectionPart constantsPart = new ConstantSectionPart(body, "Constants instantiation",
                "Specify the values of the model constants.", toolkit, this);
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
        TableSectionPart definitionsPart = new TableSectionPart(advancedArea, "Definition Override", "...", toolkit, this);
        managedForm.addPart(definitionsPart);
        // layout 
        gd = new GridData(GridData.FILL_HORIZONTAL);
        definitionsPart.getSection().setLayoutData(gd);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.widthHint = 100;
        gd.verticalSpan = 3;
        definitionsPart.getTableViewer().getTable().setLayoutData(gd);

        // new definitions
        TableSectionPart newDefinitionPart = new TableSectionPart(advancedArea, "New Definitions", "...", toolkit, this);
        managedForm.addPart(newDefinitionPart);
        // layout
        gd = new GridData(GridData.FILL_HORIZONTAL);
        newDefinitionPart.getSection().setLayoutData(gd);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.widthHint = 100;
        gd.verticalSpan = 3;
        newDefinitionPart.getTableViewer().getTable().setLayoutData(gd);

        // symmetry
        TableSectionPart symmetryPart = new TableSectionPart(advancedArea, "Symmetry", "...", toolkit, this);
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
        
        dirtyPartListeners.add(constraintListener);
    }

    protected Layout getBodyLayout()
    {
        return FormHelper.createFormGridLayout(false, 1);
    }
    
}
