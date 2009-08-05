package org.lamport.tla.toolbox.ui.property;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.ResourceBasedPreferenceStore;

/**
 * @author Simon Zambrovski
 * @version $Id$
 * @deprecated Not used 
 */
public class ModulePropertyPage extends GenericFieldEditorPropertyPage
{
    StringFieldEditor pcalParamEditor;
    
    /** (non-Javadoc)
     * Method declared on PreferencePage
     */
    public Control createContents(Composite parent)
    {
        Control contents = super.createContents(parent);
        // ensure the page has no special buttons
        noDefaultAndApplyButton();
        // setup help
        // UIHelper.setHelp(contents, IHelpConstants.MODULE_PROPERTY_PAGE);
        return contents;
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.ui.property.GenericFieldEditorPropertyPage#createFieldEditors(org.eclipse.swt.widgets.Composite)
     */
    public void createFieldEditors(Composite composite)
    {
        pcalParamEditor = new StringFieldEditor(IPreferenceConstants.PCAL_CAL_PARAMS, "PCal call arguments", composite);
        addEditor(pcalParamEditor);
    }

    public IPreferenceStore getPreferenceStore()
    {
        IResource resource = (IResource) getElement();
        return new ResourceBasedPreferenceStore(resource);
    }
    
    
    
}
