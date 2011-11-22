package org.lamport.tla.toolbox.tool.tlc.ui.wizard;

import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;

/**
 * Wizard for editing a constant assignement
 * @author Simon Zambrovski
 * @version $Id$
 */
public class AssignmentWizard extends Wizard
{
    /**
     * Currently, this flag is not used.
     */
    public final static int NONE = 0;
    /**
     * This is a flag for showing the model value,
     * ordinary assignment, set of model values,
     * and symmetric options.
     * This is currently only used by constant assignments.
     */
    public final static int SHOW_OPTION = 1;
    /**
     *  This is a flag for showing the model value
     *  and ordinary assignment options.
     *  This is currently only used by definition overrides.
     */
    public final static int SHOW_MODEL_VALUE_OPTION = 2;

    private Assignment assignment;
    private AssignmentWizardPage assignmentPage;
    private TypingWizardPage typePage;
	private WizardDialog WizardDialog;

    /**
     * Constructs the wizard that assigns values to constants, 
     * I believe it also constructs the wizard that overrides definitions. (LL)
     * The last argument is meaningful only for the wizard that assigns values
     * to constants.
     * @param fieldFlags bit mask determining fields that are visible
     * @see {@link AssignmentWizard} constants 
     */
    public AssignmentWizard(String action, String description, Assignment assignment, int fieldFlags, String helpId,
            String pageTwoHelpId)
    {
        super();
        this.assignment = assignment;
        assignmentPage = new AssignmentWizardPage(action, description, fieldFlags, helpId);
        typePage = new TypingWizardPage(action, description, pageTwoHelpId);

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

    /**
     * This returns whether the Finish button
     * should be enabled. In order for this to be
     * evaluated, getContainer().updateButtons() must
     * be called by the page whose buttons are to be
     * updated. For this particular wizard, that page
     * is a AssignmentWizardPage. Within the method
     * createControl a listener is added to the
     * text field which calls updateButtons() whenever
     * the input text is modified.
     */
    public boolean canFinish()
    {
        String inputText = assignmentPage.getInputText();
        // either on the first page, but no typing of MV set is possible, or on the second page
        // also, if on the first page, there must be an input that is not only white space
        // Modified by LL on 5 Nov 2009 to return true regardless of inputText if the model value
        // option is selected.
        return (    assignmentPage.isCurrentPage() 
        		&& !assignmentPage.isTypeInputPossible() 
        		&& (   (inputText != null && inputText.trim().length() != 0)
        		     || assignmentPage.modelValueSelected()
        			)
        		)
                || !assignmentPage.isCurrentPage();
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.wizard.Wizard#performFinish()
     */
    public boolean performFinish()
    {
        return true;
    }

	public void setWizardDialog(WizardDialog dialog) {
		WizardDialog = dialog;
	}
	
	public int getWizardDialogReturnCode() {
		return WizardDialog.getReturnCode();
	}
}
