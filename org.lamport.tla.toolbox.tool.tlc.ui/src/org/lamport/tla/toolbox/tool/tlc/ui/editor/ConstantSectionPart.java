package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.tool.tlc.ui.wizard.ConstantWizard;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ConstantSectionPart extends TableSectionPart
{
    /**
     * @param composite
     * @param title
     * @param description
     * @param toolkit
     */
    public ConstantSectionPart(Composite composite, String title, String description, FormToolkit toolkit)
    {
        super(composite, title, description, toolkit);
    }

    protected Formula doEditFormula(Formula formula)
    {
        if (formula == null) 
        {
            formula = new Assignment("test", new String[] { "a", "b" }, "me");
        }
        if (formula instanceof Assignment) 
        {
            // Create the wizard
            ConstantWizard wizard = new ConstantWizard(getSection().getText(), getSection().getDescription(), (Assignment) formula);
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
            
        } else {
            return super.doEditFormula(formula);
        }

    }
}
