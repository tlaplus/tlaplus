package org.lamport.tla.toolbox.ui.property;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * Represents specification properties
 * @author Simon Zambrovski
 * @version $Id$
 */
public class SpecPropertyPage extends GenericFieldEditorPropertyPage
{

    
    protected Control createContents(Composite parent)
    {
        Control control = super.createContents(parent);
        UIHelper.setHelp(control, IHelpConstants.SPEC_PROPERTY_PAGE);
        return control;
    }

    public void createFieldEditors(Composite composite)
    {
        StringFieldEditor rootFileEditor = new StringFieldEditor(IPreferenceConstants.P_PROJECT_ROOT_FILE,
                "Specification root module", composite);
        addEditor(rootFileEditor);
    }
   
    
    protected IPreferenceStore doGetPreferenceStore()
    {
        Spec spec = (Spec) getElement();
        return PreferenceStoreHelper.getProjectPreferenceStore(spec.getProject());
    }







}
