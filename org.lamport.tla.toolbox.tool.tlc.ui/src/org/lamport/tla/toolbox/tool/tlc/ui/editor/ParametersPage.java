package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Layout;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParametersPage extends BasicFormPage
{

    public static final String ID = "Parameters";

    public ParametersPage(FormEditor editor)
    {
        super(editor, ParametersPage.ID, "Parameters");
        this.helpId = IHelpConstants.PARAMETERS_MODEL_PAGE;
    }

    protected void createContent(IManagedForm managedForm)
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
        gd.verticalSpan = 2;
        definitionsPart.getTableViewer().getTable().setLayoutData(gd);

        // new definitions
        TableSectionPart newDefinitionPart = new TableSectionPart(advancedArea, "New Definitions", "...", toolkit);
        managedForm.addPart(newDefinitionPart);
        // layout
        gd = new GridData(GridData.FILL_HORIZONTAL);
        newDefinitionPart.getSection().setLayoutData(gd);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.widthHint = 100;
        gd.verticalSpan = 2;
        newDefinitionPart.getTableViewer().getTable().setLayoutData(gd);

        // symmetry
        TableSectionPart symmetryPart = new TableSectionPart(advancedArea, "Symmetry", "...", toolkit);
        managedForm.addPart(symmetryPart);
        // layout
        gd = new GridData(GridData.FILL_HORIZONTAL);
        symmetryPart.getSection().setLayoutData(gd);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.widthHint = 100;
        gd.verticalSpan = 2;
        symmetryPart.getTableViewer().getTable().setLayoutData(gd);

        // constraint
        Section constraintSection = FormHelper.createSectionComposite(advancedArea, "Constraint", "...", toolkit,
                Section.DESCRIPTION | Section.TITLE_BAR | Section.TWISTIE | Section.COMPACT, getExpansionListener());

        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.horizontalSpan = 3;
        constraintSection.setLayoutData(gd);

        Composite constraintArea = (Composite) constraintSection.getClient();
        SourceViewer constraintSource = FormHelper.createSourceViewer(toolkit, constraintArea, SWT.V_SCROLL);
        // layout of the source viewer
        TableWrapData twd = new TableWrapData(TableWrapData.FILL);
        twd.heightHint = 60;
        twd.grabHorizontal = true;
        constraintSource.getTextWidget().setLayoutData(twd);

    }

    protected Layout getBodyLayout()
    {
        return new GridLayout();
    }
}
