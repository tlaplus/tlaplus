package org.lamport.tla.toolbox.tool.tlc.ui.wizard;

import org.eclipse.jface.wizard.Wizard;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;

/**
 * Wizard for editing a constant assignement
 * @author Simon Zambrovski
 * @version $Id$
 */
public class AssignmentWizard extends Wizard
{
    private AssignmentWizardPage page;

    /**
     * 
     */
    public AssignmentWizard(String action, String description, Assignment initialContent)
    {
        super();
        page = new AssignmentWizardPage(action, description, initialContent);
    }

    /*
     * @see org.eclipse.jface.wizard.Wizard#performFinish()
     */
    public boolean performFinish()
    {
        return true;
    }

    public void addPages()
    {
        addPage(page);
    }

    /**
     * retrieves the formula
     * @return
     */
    public Assignment getFormula()
    {
        return page.getAssignment();
    }
}
