package org.lamport.tla.toolbox;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.core.runtime.preferences.DefaultScope;
import org.eclipse.equinox.internal.p2.ui.sdk.scheduler.AutomaticUpdatePlugin;
import org.eclipse.equinox.internal.p2.ui.sdk.scheduler.PreferenceConstants;
import org.osgi.service.prefs.Preferences;

public class TLAPreferenceInitializer extends AbstractPreferenceInitializer {

	/* (non-Javadoc)
	 * @see org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer#initializeDefaultPreferences()
	 */
	public void initializeDefaultPreferences() {
		// initialize the default scope
		Preferences node = new DefaultScope().getNode(AutomaticUpdatePlugin.PLUGIN_ID);
		node.putBoolean(PreferenceConstants.PREF_AUTO_UPDATE_ENABLED, true);
	}
}
