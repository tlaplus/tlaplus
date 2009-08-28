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
    public final static int NONE = 0;
    public final static int SHOW_OPTION = 1;

    private Assignment assignment;
    private AssignmentWizardPage assignmentPage;
    private TypingWizardPage typePage;

    /**
     * Constructs the assignment wizard
     * @param fieldFlags bit mask determining fields that are visible
     * @see {@link AssignmentWizard} constants 
     */
    public AssignmentWizard(String action, String description, Assignment assignment, int fieldFlags)
    {
        super();
        this.assignment = assignment;
        assignmentPage = new AssignmentWizardPage(action, description, fieldFlags);
        typePage = new TypingWizardPage(action, description);

    }

    public void addPages()
    {
        addPage(assignmentPage);
        addPage(typePage);
    }

    /**
     * retrieves the formula
     * @return
     */
    public Assignment getFormula()
    {
        return this.assignment;
    }

    public boolean canFinish()
    {
        // either on the first page, but no typing of MV set is possible, or on the second page
        return (assignmentPage.isCurrentPage() && !assignmentPage.isTypeInputPossible())
                || !assignmentPage.isCurrentPage();
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.wizard.Wizard#performFinish()
     */
    public boolean performFinish()
    {
        return true;
    }
}
