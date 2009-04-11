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
    public final static int NONE                 = 0;
    public final static int MAKE_MODEL_VALUE     = 1;
    public final static int MAKE_SET_MODEL_VALUE = 2;
    
    private AssignmentWizardPage assignmentPage;

    /**
     * Constructs the assignment wizard
     * @param fieldFlags bit mask determining fields that are visible
     * @see {@link AssignmentWizard} constants 
     */
    public AssignmentWizard(String action, String description, Assignment initialContent, int fieldFlags)
    {
        super();
        assignmentPage = new AssignmentWizardPage(action, description, initialContent, fieldFlags);
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
        addPage(assignmentPage);
    }

    /**
     * retrieves the formula
     * @return
     */
    public Assignment getFormula()
    {
        return assignmentPage.getAssignment();
    }
}
