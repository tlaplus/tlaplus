package org.lamport.tla.toolbox.tool.tlc.ui.editor.part;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.SectionPart;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.BasicFormPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.validator.IValidateble;

/**
 * Section part implementing validateable interface
 * On validation request it delegates the validation to the editor page
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class VSectionPart extends SectionPart implements IValidateble
{
    private BasicFormPage page;
    
    
    public VSectionPart(Composite parent, FormToolkit toolkit, int style, BasicFormPage page)
    {
        super(parent, toolkit, style);
        this.page = page;
    }

    public VSectionPart(Section section, BasicFormPage page)
    {
        super(section);
        this.page = page;
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.ui.editor.validator.IValidateble#validate(org.eclipse.jface.text.IDocument, org.eclipse.jface.text.IDocument)
     */
    public void validate()
    {
        page.validate();
    }

}
