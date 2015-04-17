package org.lamport.tla.toolbox.ui.property;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Path;
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
	private StringFieldEditor rootFileEditor;
	private StringFieldEditor directorySizeEditor;
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
		rootFileEditor = new StringFieldEditor(
				IPreferenceConstants.P_PROJECT_ROOT_FILE,
				"Specification root module", composite);
		addEditor(rootFileEditor);
		rootFileEditor.getTextControl(composite).setEditable(false);

		StringFieldEditor pcalParamEditor = new StringFieldEditor(
				IPreferenceConstants.PCAL_CAL_PARAMS, "PlusCal call arguments",
				composite);
		addEditor(pcalParamEditor);

		directorySizeEditor = new StringFieldEditor(
				"DoesNotExistIsIrrelevant",
				"Size of .toolbox directory in kbytes", composite);
		addEditor(directorySizeEditor);
		directorySizeEditor.getTextControl(composite).setEditable(false);

		libraryPathComposite = new LibraryPathComposite(this);

	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.ui.property.GenericFieldEditorPropertyPage#initialize()
	 */
	protected void initialize() {
		super.initialize();	
		
		/*
		 * The preference store keeps an Eclipse specific relative file path. It
		 * has to be resolved to the OS specific path.
		 * 
		 * @see PreferenceStoreHelper#storeRootFilename(..)
		 */
		final IPreferenceStore preferenceStore = getPreferenceStore();

		final Spec spec = (Spec) getElement();
		final IProject project = spec.getProject();

		final String relativePath = preferenceStore.getString(IPreferenceConstants.P_PROJECT_ROOT_FILE);
		final IFile resolvedFile = project.getFile(new Path(relativePath).lastSegment());
		rootFileEditor.setStringValue(resolvedFile.getLocation().toOSString());
		
		directorySizeEditor.setStringValue(Long.toString(spec.getSize() / 1000L)); // convert to KB
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
