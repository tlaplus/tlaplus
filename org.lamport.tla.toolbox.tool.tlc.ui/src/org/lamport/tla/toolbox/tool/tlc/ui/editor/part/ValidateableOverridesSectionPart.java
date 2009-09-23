package org.lamport.tla.toolbox.tool.tlc.ui.editor.part;

import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.ui.dialog.FilteredDefinitionSelectionDialog;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.DataBindingManager;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.BasicFormPage;
import org.lamport.tla.toolbox.tool.tlc.ui.wizard.AssignmentWizard;
import org.lamport.tla.toolbox.tool.tlc.ui.wizard.AssignmentWizardPage;

import tla2sany.semantic.OpDefNode;

/**
 * Section part for the DefinitionOverride section of the Advanced Options page
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ValidateableOverridesSectionPart extends ValidateableConstantSectionPart
{

    public ValidateableOverridesSectionPart(Composite composite, String title, String description, FormToolkit toolkit,
            int flags, BasicFormPage page)
    {
        super(composite, title, description, toolkit, flags, page, DataBindingManager.SEC_DEFINITION_OVERRIDE);
    }

    protected Assignment doEditFormula(Assignment formula)
    {
        // add -> let the user select the definition to override
        if (formula == null)
        {
            FilteredDefinitionSelectionDialog definitionSelection = new FilteredDefinitionSelectionDialog(this
                    .getSection().getShell(), false, ToolboxHandle.getCurrentSpec().getValidRootModule());

            definitionSelection.setTitle("Select Definition to Override");
            // It would be nice to add help to this dialog. The following command will
            // add a help button. However, I have no idea how to attach an help
            // to that button.
            //
            // definitionSelection.setHelpAvailable(true);

            definitionSelection
                    .setMessage("Type definition to override or select from the list below\n(?= any character, *= any string)");
            definitionSelection.setInitialPattern("?");
            if (Window.OK == definitionSelection.open())
            {
                OpDefNode result = (OpDefNode) (definitionSelection.getResult())[0];
                formula = new Assignment(result.getName().toString(), Assignment.getArrayOfEmptyStrings(result
                        .getSource().getNumberOfArgs()), "");
            } else
            {
                return null;
            }
        }

        // Create the wizard
        AssignmentWizard wizard = new AssignmentWizard(getSection().getText(), getSection().getDescription(),
                (Assignment) formula, AssignmentWizard.NONE, AssignmentWizardPage.DEF_OVERRIDE_WIZARD_ID);
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
     * create the buttons
     */
    protected void createButtons(Composite sectionArea, FormToolkit toolkit, boolean add, boolean edit, boolean remove)
    {
        doCreateButtons(sectionArea, toolkit, true, true, true);
    }
}
