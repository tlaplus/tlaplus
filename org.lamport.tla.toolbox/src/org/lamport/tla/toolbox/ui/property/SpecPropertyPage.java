package org.lamport.tla.toolbox.ui.property;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.preference.LibraryPathComposite;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * Represents specification properties
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class SpecPropertyPage extends GenericFieldEditorPropertyPage {
	private StringFieldEditor pcalParamEditor;
	private LibraryPathComposite libraryPathComposite;

	protected Control createContents(Composite parent) {
		Control control = super.createContents(parent);

		// ensure the page has no special buttons
		noDefaultAndApplyButton();

		UIHelper.setHelp(control, IHelpConstants.SPEC_PROPERTY_PAGE);
		return control;
	}

	public void createFieldEditors(Composite composite) {
		// TODO change root file
		StringFieldEditor rootFileEditor = new StringFieldEditor(
				IPreferenceConstants.P_PROJECT_ROOT_FILE,
				"Specification root module", composite);
		addEditor(rootFileEditor);
		rootFileEditor.getTextControl(composite).setEditable(false);

		pcalParamEditor = new StringFieldEditor(
				IPreferenceConstants.PCAL_CAL_PARAMS, "PlusCal call arguments",
				composite);
		addEditor(pcalParamEditor);

		StringFieldEditor directorySizeEditor = new StringFieldEditor(
				IPreferenceConstants.P_PROJECT_TOOLBOX_DIR_SIZE,
				"Size of .toolbox directory in kbytes", composite);
		addEditor(directorySizeEditor);
		directorySizeEditor.getTextControl(composite).setEditable(false);

		libraryPathComposite = new LibraryPathComposite(this);

	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.preference.PreferencePage#doGetPreferenceStore()
	 */
	protected IPreferenceStore doGetPreferenceStore() {
		Spec spec = (Spec) getElement();
		return PreferenceStoreHelper.getProjectPreferenceStore(spec
				.getProject());
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.ui.property.GenericFieldEditorPropertyPage#performDefaults()
	 */
	protected void performDefaults() {
		libraryPathComposite.performInit();
		super.performDefaults();
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.ui.property.GenericFieldEditorPropertyPage#performOk()
	 */
	public boolean performOk() {
		libraryPathComposite.applyChanges();
		return super.performOk();
	}
}
