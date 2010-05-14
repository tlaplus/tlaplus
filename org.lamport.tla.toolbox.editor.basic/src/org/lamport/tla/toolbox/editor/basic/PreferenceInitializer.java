/**
 * 
 */
package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;
import org.lamport.tla.toolbox.editor.basic.preferences.EditorPreferencePage;

/**
 * @author lamport
 *
 */
public class PreferenceInitializer extends AbstractPreferenceInitializer
{

    /**
     * 
     */
    public PreferenceInitializer()
    {
        // TODO Auto-generated constructor stub
    }

    /* (non-Javadoc)
     * @see org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer#initializeDefaultPreferences()
     */
    public void initializeDefaultPreferences()
    {
        IPreferenceStore store = TLAEditorActivator.getDefault().getPreferenceStore();
        store.setDefault(EditorPreferencePage.EDITOR_RIGHT_MARGIN, 
                         EditorPreferencePage.EDITOR_RIGHT_MARGIN_DEFAULT);

    }

}
