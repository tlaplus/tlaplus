package org.lamport.tla.toolbox.ui.property;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.dialogs.PropertyPage;

/**
 * Represents specification properties
 * @author Simon Zambrovski
 * @version $Id$
 */
public class SpecPropertyPage extends PropertyPage 
{

    /*
     * @see org.eclipse.jface.preference.PreferencePage#createContents(org.eclipse.swt.widgets.Composite)
     */
    protected Control createContents(Composite parent)
    {
        Composite composite = new Composite(parent, SWT.NONE);
        return composite;
    }

}
