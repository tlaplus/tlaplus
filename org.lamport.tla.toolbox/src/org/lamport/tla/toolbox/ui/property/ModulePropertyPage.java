package org.lamport.tla.toolbox.ui.property;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.ResourceBasedPreferenceStore;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModulePropertyPage extends GenericFieldEditorPropertyPage
{
    BooleanFieldEditor algorithmFoundEditor;
    
    /** (non-Javadoc)
     * Method declared on PreferencePage
     */
    public Control createContents(Composite parent)
    {
        Control contents = super.createContents(parent);
        // ensure the page has no special buttons
        noDefaultAndApplyButton();
        // TODO
        // PlatformUI.getWorkbench().getHelpSystem().setHelp(getControl(), );
        return contents;
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.ui.property.GenericFieldEditorPropertyPage#createFieldEditors(org.eclipse.swt.widgets.Composite)
     */
    public void createFieldEditors(Composite composite)
    {
        algorithmFoundEditor = new BooleanFieldEditor(IPreferenceConstants.CONTAINS_PCAL_ALGORITHM, "PCal Algorithm found", composite);
        addEditor(algorithmFoundEditor);
        
    }

    public IPreferenceStore getPreferenceStore()
    {
        IResource resource = (IResource) getElement();
        return new ResourceBasedPreferenceStore(resource);
    }
    
    
    
}
