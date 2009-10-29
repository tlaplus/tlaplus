package org.lamport.tla.toolbox.tool.tlc.ui.wizard;

import org.eclipse.jface.text.Document;
import org.eclipse.jface.wizard.Wizard;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;

/**
 * A wizard for entering formulas
 * @author Simon Zambrovski
 * @version $Id$
 */
public class FormulaWizard extends Wizard
{
    private FormulaWizardPage page;

    /**
     * 
     */
    public FormulaWizard(String action, String description)
    {
        super();
        page = new FormulaWizardPage(action, description);
    }

    /*
     * @see org.eclipse.jface.wizard.Wizard#performFinish()
     */
    public boolean performFinish()
    {
        return true;
    }

    /**
     * This returns whether the Finish button
     * should be enabled. In order for this to be
     * evaluated, getContainer().updateButtons() must
     * be called by the page whose buttons are to be
     * updated. For this particular wizard, that page
     * is a FormulaWizardPage. Within the method
     * createControl a listener is added to the
     * text field which calls updateButtons() whenever
     * the input text is modified.
     */
    public boolean canFinish()
    {
        // the user can finish if something other than
        // simply white space has been entered
        String inputText = page.getDocument().get();
        return inputText != null && inputText.trim().length() != 0;
    }

    public void addPages()
    {
        addPage(page);
    }

    /**
     * retrieves the formula
     * @return
     */
    public Formula getFormula()
    {
        return new Formula(FormHelper.trimTrailingSpaces(page.getDocument().get()));
    }

    /**
     * Sets a formula to edit
     * @param initialContent
     */
    public void setFormula(Formula initialContent)
    {
        Document doc;
        if (initialContent == null)
        {
            doc = new Document();
        } else
        {
            doc = new Document(initialContent.getFormula());
        }
        page.setDocument(doc);
    }
}
