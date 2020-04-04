package org.lamport.tla.toolbox.tool.tla2tex.preference;

import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.lamport.tla.toolbox.tool.tla2tex.TLA2TeXActivator;

/**
 * Preference page for TLA2TeX
 * 
 * @author Daniel Ricketts
 * @version $Id$
 */
public class TLA2TeXPreferencePage extends FieldEditorPreferencePage implements
		IWorkbenchPreferencePage {

	public TLA2TeXPreferencePage() {
		super(GRID);
		setPreferenceStore(TLA2TeXActivator.getDefault().getPreferenceStore());
		setDescription("PDF Viewer Preferences");
	}

	public TLA2TeXPreferencePage(int style) {
		super(style);
	}

	public TLA2TeXPreferencePage(String title, int style) {
		super(title, style);
	}

	public TLA2TeXPreferencePage(String title, ImageDescriptor image, int style) {
		super(title, image, style);
	}

	protected void createFieldEditors() {
		if (Platform.getOS().equals(Platform.OS_MACOSX)) {
			addField(new BooleanFieldEditor(
					ITLA2TeXPreferenceConstants.HAVE_OS_OPEN_PDF,
					"Have your OS open PDFs", getFieldEditorParent()));
		} else {
			addField(new BooleanFieldEditor(
					ITLA2TeXPreferenceConstants.EMBEDDED_VIEWER,
					"&Use built-in PDF viewer", getFieldEditorParent()));
		}
		
		// Preference to regenerate PDF upon spec save?
		addField(new BooleanFieldEditor(
				ITLA2TeXPreferenceConstants.AUTO_REGENERATE, "&Regenerate pretty-printed PDF on spec save (takes effect once spec re-opened).",
				getFieldEditorParent()));

		addField(new BooleanFieldEditor(
				ITLA2TeXPreferenceConstants.SHADE_COMMENTS, "&Shade comments",
				getFieldEditorParent()));
        addField(new BooleanFieldEditor(
                ITLA2TeXPreferenceConstants.NO_PCAL_SHADE, "&Do not shade PlusCal code",
                getFieldEditorParent()));
		addField(new BooleanFieldEditor(
				ITLA2TeXPreferenceConstants.NUMBER_LINES, "&Number lines",
				getFieldEditorParent()));
		addField(new StringFieldEditor(
				ITLA2TeXPreferenceConstants.DOT_COMMAND,
				"&Specify dot command", getFieldEditorParent()));
		addField(new StringFieldEditor(
				ITLA2TeXPreferenceConstants.LATEX_COMMAND,
				"&Specify pdflatex command", getFieldEditorParent()));
		addField(new DoubleFieldEditor(ITLA2TeXPreferenceConstants.GRAY_LEVEL,
				"&Specify gray level (between 0.0 and 1.0)",
				getFieldEditorParent(), 0, 1));
	}

	public void init(IWorkbench workbench) {
		// nop
	}
}
