package org.lamport.tla.toolbox.tool.tlc.ui.editor.preference;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

public class ModelEditorPreferenceInitializer  extends AbstractPreferenceInitializer {
	public void initializeDefaultPreferences() {
		final IPreferenceStore uiPreferencesStore = TLCUIActivator.getDefault().getPreferenceStore();

        uiPreferencesStore.setDefault(IModelEditorPreferenceConstants.I_MODEL_EDITOR_SHOW_ECE_AS_TAB, false);
        uiPreferencesStore.setDefault(IModelEditorPreferenceConstants.I_OVERRIDDEN_DEFINITION_STYLE,
        		IModelEditorPreferenceConstants.I_OVERRIDDEN_DEFINITION_STYLE_MODULE_NAME);
	}
}
