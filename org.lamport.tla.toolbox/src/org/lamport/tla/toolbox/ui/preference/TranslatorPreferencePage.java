package org.lamport.tla.toolbox.ui.preference;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

public class TranslatorPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage
{
    
    /**
     * Constructor
     */
    public TranslatorPreferencePage()
    {
        super(GRID);
        setPreferenceStore(PreferenceStoreHelper.getInstancePreferenceStore());
        setDescription("PCal Translator preferences");
    }

    protected Control createContents(Composite parent)
    {
        Control pageControl = super.createContents(parent);
        UIHelper.setHelp(pageControl, IHelpConstants.TRANSLATOR_PREFERENCE_PAGE);
        return pageControl;
    }

    /**
     * Create field editors
     */
    protected void createFieldEditors()
    {

        addField(new BooleanFieldEditor(IPreferenceConstants.I_TRANSLATE_POPUP_ERRORS,
                "&Popup problem window on translator errors", getFieldEditorParent()));

        addField(new BooleanFieldEditor(IPreferenceConstants.I_TRANSLATE_MODULE_ON_MODIFY,
                "&Automatic re-translate module", getFieldEditorParent()));
    }

    public void init(IWorkbench workbench)
    {

    }
    
    
    protected void initialize()
    {
        // sync the auto-build
        // getPreferenceStore().setValue(IPreferenceConstants.I_PARSE_MODULE_ON_MODIFY, ResourcesPlugin.getWorkspace().isAutoBuilding());
        super.initialize();
    }
}
