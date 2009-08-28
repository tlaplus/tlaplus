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
