package org.lamport.tla.toolbox.ui.property;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.widgets.Composite;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * Represents specification properties
 * @author Simon Zambrovski
 * @version $Id$
 */
public class SpecPropertyPage extends GenericFieldEditorPropertyPage
{


    /**
     * 
     */
    public void createFieldEditors(Composite composite)
    {
        // TODO
        // PlatformUI.getWorkbench().getHelpSystem().setHelp(getControl(), );

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
