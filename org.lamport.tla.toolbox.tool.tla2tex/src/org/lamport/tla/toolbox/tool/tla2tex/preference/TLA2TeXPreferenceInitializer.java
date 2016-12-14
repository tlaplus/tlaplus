package org.lamport.tla.toolbox.tool.tla2tex.preference;

import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;
import org.lamport.tla.toolbox.tool.tla2tex.TLA2TeXActivator;

/**
 * Gives default preferences for TLA2TeX
 * 
 * @author Daniel Ricketts
 * @version $Id$
 */
public class TLA2TeXPreferenceInitializer extends AbstractPreferenceInitializer {

	public void initializeDefaultPreferences() {
		IPreferenceStore store = TLA2TeXActivator.getDefault()
				.getPreferenceStore();
		store.setDefault(ITLA2TeXPreferenceConstants.SHADE_COMMENTS, true);
		store.setDefault(ITLA2TeXPreferenceConstants.NO_PCAL_SHADE, false);
        store.setDefault(ITLA2TeXPreferenceConstants.NUMBER_LINES, false);
		store.setDefault(ITLA2TeXPreferenceConstants.LATEX_COMMAND, "pdflatex");
		store.setDefault(ITLA2TeXPreferenceConstants.GRAY_LEVEL, "0.85");
		if (Platform.getOS().equals(Platform.OS_MACOSX)) {
			// Support for the built-in viewer has ended on MACOSX, thus disable
			// even if user enabled it in an earlier Toolbox release.
			store.setValue(ITLA2TeXPreferenceConstants.EMBEDDED_VIEWER, false);
		} else {
			store.setDefault(ITLA2TeXPreferenceConstants.EMBEDDED_VIEWER, true);
		}
	}
}
