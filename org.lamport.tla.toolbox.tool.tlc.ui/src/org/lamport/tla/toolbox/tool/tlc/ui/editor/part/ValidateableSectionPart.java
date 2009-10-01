package org.lamport.tla.toolbox.tool.tlc.ui.editor.part;

import org.eclipse.ui.forms.SectionPart;
import org.eclipse.ui.forms.widgets.Section;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.BasicFormPage;

/**
 * Section part implementing validate-able interface
 * On validation request it delegates the validation to the editor page
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ValidateableSectionPart extends SectionPart implements IValidateble
{
    private BasicFormPage page;

    /**
     * Creates a wrapper around the section
     * @param section
     * @param page
     */
    public ValidateableSectionPart(Section section, BasicFormPage page, String sectionName)
    {
        super(section);
        this.page = page;
        page.getDataBindingManager().bindSection(this, sectionName, page.getId());
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.ui.editor.validator.IValidateble#validate(org.eclipse.jface.text.IDocument, org.eclipse.jface.text.IDocument)
     */
    public void validate()
    {
        page.validatePage(false);
    }

    public void commit(boolean onSave)
    {
        // commit the part on save, but not on other events
        if (onSave) 
        {
            // System.out.println("commit() of the SectionPart " + getSection().getText() + " has value of " + isDirty());
            super.commit(onSave);
        }
    }
    
    
    
    
    
    
    

}
