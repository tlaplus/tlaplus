package org.lamport.tla.toolbox.tool.tlc.ui.wizard;

import org.eclipse.jface.text.Document;
import org.eclipse.jface.wizard.Wizard;

/**
 * A wizard for entering formulas
 * @author Simon Zambrovski
 * @version $Id$
 */
public class FormulaWizard extends Wizard
{
    private FormulaPage page;

    /**
     * 
     */
    public FormulaWizard(String action, String description)
    {
        super();
        page = new FormulaPage(action, description);
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
    public String getFormula()
    {
        return page.getDocument().get();
    }
    
    /**
     * Sets a formula to edit
     * @param initialContent
     */
    public void setFormula(String initialContent)
    {
        Document doc;
        if (initialContent == null) 
        {
            doc = new Document();
        } else {
            doc = new Document(initialContent);
        }
        page.setDocument(doc);
    }
}
