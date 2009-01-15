package org.lamport.tla.toolbox.ui.preference;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * Preferences for TLA+ Parser
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParserPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage
{

    /**
     * Constructor
     */
    public ParserPreferencePage()
    {
        super(GRID);
        setPreferenceStore(PreferenceStoreHelper.getInstancePreferenceStore());
        setDescription("TLA+ Parser preferences");

    }

    /**
     * Create field editors
     */
    protected void createFieldEditors()
    {
        addField(new BooleanFieldEditor(IPreferenceConstants.P_PARSER_RUN_ON_MODIFICATION, "&Run parser on file modifications",
                getFieldEditorParent()));

        addField(new BooleanFieldEditor(IPreferenceConstants.P_PARSER_POPUP_ERRORS, "&Popup problem window on parse errors",
                getFieldEditorParent()));
    }


    public void init(IWorkbench workbench)
    {

    }

}
