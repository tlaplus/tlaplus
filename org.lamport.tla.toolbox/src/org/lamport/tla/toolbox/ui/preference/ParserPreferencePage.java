package org.lamport.tla.toolbox.ui.preference;

import org.eclipse.core.resources.IWorkspaceDescription;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
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

    protected Control createContents(Composite parent)
    {
        Control pageControl = super.createContents(parent);
        UIHelper.setHelp(pageControl, IHelpConstants.PARSER_PREFERENCE_PAGE);
        return pageControl;
    }

    /**
     * Create field editors
     */
    protected void createFieldEditors()
    {

        addField(new BooleanFieldEditor(IPreferenceConstants.I_PARSER_POPUP_ERRORS,
                "&Popup problem window on parse errors", getFieldEditorParent()));

        addField(new BooleanFieldEditor(IPreferenceConstants.I_PARSE_MODULE_ON_MODIFY,
                "&Automatic re-parse module", getFieldEditorParent()));

        addField(new BooleanFieldEditor(IPreferenceConstants.I_PARSE_FILES_ON_MODIFY,
                "&Automatic re-parse all module dependent files (experimental)", getFieldEditorParent()));

        addField(new BooleanFieldEditor(IPreferenceConstants.I_PARSE_SPEC_ON_MODIFY,
                "&Automatic re-parse specification if depends on module", getFieldEditorParent()));
        
    }

    public void init(IWorkbench workbench)
    {

    }
    
    
    protected void initialize()
    {
        // sync the auto-build
        getPreferenceStore().setValue(IPreferenceConstants.I_PARSE_MODULE_ON_MODIFY, ResourcesPlugin.getWorkspace().isAutoBuilding());
        super.initialize();
    }

    
    
    protected void performApply()
    {
        super.performApply();
        this.setAutoBuilding();
    }

    public boolean performOk()
    {
        boolean result = super.performOk();
        this.setAutoBuilding();
        return result;
    }

    /**
     * Sets the value of the workspace auto-build to the module auto-build 
     */
    private void setAutoBuilding()
    {
        boolean autoBuildModule = getPreferenceStore().getBoolean(IPreferenceConstants.I_PARSE_MODULE_ON_MODIFY);
        
        // set the workspace auto-build flag
        IWorkspaceDescription description = ResourcesPlugin.getWorkspace()
                .getDescription();
        if (autoBuildModule != ResourcesPlugin.getWorkspace().isAutoBuilding()) {
            try {
                description.setAutoBuilding(autoBuildModule);
                ResourcesPlugin.getWorkspace().setDescription(description);
            } catch (CoreException e) {
                // TODO
                e.printStackTrace();
            }
        }
    }

}
