package org.lamport.tla.toolbox.tool.tlc.ui.editor.preference;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Preference pane for the Model Editor preferences page.
 */
public class ModelEditorPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
	public ModelEditorPreferencePage() {
        super(GRID);
        
        // Copy preference value to non-ui plugin.
        TLCUIActivator.getDefault().getPreferenceStore().addPropertyChangeListener(new IPropertyChangeListener() {
			@Override
			public void propertyChange(PropertyChangeEvent event) {
				final IPreferenceStore store = TLCActivator.getDefault().getPreferenceStore();
				if (TLCActivator.I_TLC_SNAPSHOT_KEEP_COUNT.equals(event.getProperty())) {
					store.setValue(TLCActivator.I_TLC_SNAPSHOT_KEEP_COUNT, (int)event.getNewValue());
				}
			}
		});
		setPreferenceStore(TLCUIActivator.getDefault().getPreferenceStore());
        setDescription("Model Editor preferences");
    }

	protected Control createContents(Composite parent) {
        final Control pageControl = super.createContents(parent);
        UIHelper.setHelp(pageControl, IHelpConstants.MODEL_EDITOR_PREFERENCE_PAGE);
        return pageControl;
    }

	protected void createFieldEditors() {
        addField(new BooleanFieldEditor(IModelEditorPreferenceConstants.I_MODEL_EDITOR_SHOW_ECE_AS_TAB,
                "Show Evaluate Constant Expression in its own tab", getFieldEditorParent()));
        
        final String[][] overrideDisplays = {
        		{ "Definition [Module Name]",
        			IModelEditorPreferenceConstants.I_OVERRIDDEN_DEFINITION_STYLE_MODULE_NAME },
        		{ "InstanceName!Definition",
        			IModelEditorPreferenceConstants.I_OVERRIDDEN_DEFINITION_STYLE_INSTANCE_NAME }
        };
        addField(new ComboFieldEditor(IModelEditorPreferenceConstants.I_OVERRIDDEN_DEFINITION_STYLE,
        		"Definition Override display style", overrideDisplays, getFieldEditorParent()));
    }

    public void init(IWorkbench workbench) { }
}
