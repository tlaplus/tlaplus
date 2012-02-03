package org.lamport.tla.toolbox.ui.preference;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * This class represents the general preference page that
 * is contributed to the Preferences dialog. By 
 * subclassing <samp>FieldEditorPreferencePage</samp>, we
 * can use the field support built into JFace that allows
 * us to create a page that is small and knows how to 
 * save, restore and apply itself.
 * <p>
 * This page is used to modify preferences only. They
 * are stored in the preference store that belongs to
 * the main plug-in class. That way, preferences can
 * be accessed directly via the preference store.
 * @author Simon Zambrovski
 * @version $Id$
 */
public class GeneralPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage
{
    /**
     * The default value for the minimum size (in kbytes) of storage occupied by
     * the spec that is displayed.
     */
    public static final int MIN_DISPLAYED_SIZE_DEFAULT = 50000;
	private LibraryPathComposite libraryPathComposite;
    
    public GeneralPreferencePage()
    {
        super(GRID);
        setPreferenceStore(PreferenceStoreHelper.getInstancePreferenceStore());
        setDescription("General toolbox preferences");
    }
    
    protected Control createContents(Composite parent)
    {
        Control pageControl = super.createContents(parent);
        
        libraryPathComposite = new LibraryPathComposite(this);
        
        UIHelper.setHelp(pageControl, IHelpConstants.GENERAL_PREFERENCE_PAGE);
        return pageControl;
    }
    
    /**
     * Creates the field editors. Field editors are abstractions of
     * the common GUI blocks needed to manipulate various types
     * of preferences. Each field editor knows how to save and
     * restore itself.
     */
    public void createFieldEditors()
    {
        /*
        addField(new DirectoryFieldEditor(PreferenceConstants.P_PATH, "&Directory preference:", getFieldEditorParent()));
        addField(new BooleanFieldEditor(PreferenceConstants.P_BOOLEAN, "&An example of a boolean preference",
                getFieldEditorParent()));

        addField(new RadioGroupFieldEditor(PreferenceConstants.P_CHOICE, "An example of a multiple-choice preference",
                1, new String[][] { { "&Choice 1", "choice1" }, { "C&hoice 2", "choice2" } }, getFieldEditorParent()));
        addField(new StringFieldEditor(PreferenceConstants.P_STRING, "A &text preference:", getFieldEditorParent()));
        */
        addField(new BooleanFieldEditor(IPreferenceConstants.I_RESTORE_LAST_SPEC,
                "&Continue Previous Session on Restart", getFieldEditorParent()));
        
        IntegerFieldEditor minStorageSizeEditor = 
             new IntegerFieldEditor(IPreferenceConstants.I_MIN_DISPLAYED_SIZE, 
                "&Minimum spec storage displayed (in kilobytes)", getFieldEditorParent());
        addField(minStorageSizeEditor);
        minStorageSizeEditor.setValidRange(0, 2000000);
    }

    /**
     * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
     */
    public void init(IWorkbench workbench)
    {
    }

	
	/* (non-Javadoc)
	 * @see org.eclipse.jface.preference.PreferencePage#performOk()
	 */
	public boolean performOk() {
		libraryPathComposite.applyChanges();
		return super.performOk();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.preference.PreferencePage#performApply()
	 */
	protected void performApply() {
		libraryPathComposite.applyChanges();
		super.performApply();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.preference.PreferencePage#performDefaults()
	 */
	protected void performDefaults() {
		libraryPathComposite.performInit();
		super.performDefaults();
	}
}