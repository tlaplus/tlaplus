package org.lamport.tla.toolbox.tool.tla2tex.preference;

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
		store.setDefault(ITLA2TeXPreferenceConstants.NUMBER_LINES, false);
		store.setDefault(ITLA2TeXPreferenceConstants.LATEX_COMMAND, "pdflatex");
		store.setDefault(ITLA2TeXPreferenceConstants.GRAY_LEVEL, "0.85");
		store.setDefault(ITLA2TeXPreferenceConstants.EMBEDDED_VIEWER, true);
	}
}
