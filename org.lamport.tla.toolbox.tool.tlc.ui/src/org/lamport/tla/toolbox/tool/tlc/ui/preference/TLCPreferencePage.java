package org.lamport.tla.toolbox.tool.tlc.ui.preference;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.IntegerFieldEditor;
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
 * Preferences for TLC
 * @author Simon Zambrovski
 */
public class TLCPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage
{

    /**
     * Constructor
     */
    public TLCPreferencePage()
    {
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
        setDescription("TLC Model Checker preferences");
    }

    protected Control createContents(Composite parent)
    {
        Control pageControl = super.createContents(parent);
        UIHelper.setHelp(pageControl, IHelpConstants.TLC_PREFERENCE_PAGE);
        return pageControl;
    }

    /**
     * Create field editors
     */
    protected void createFieldEditors()
    {
        addField(new BooleanFieldEditor(ITLCPreferenceConstants.I_TLC_POPUP_ERRORS, "&Always pop up TLC errors view",
                getFieldEditorParent()));

        addField(new BooleanFieldEditor(ITLCPreferenceConstants.I_TLC_REVALIDATE_ON_MODIFY,
                "&Re-validate model on save", getFieldEditorParent()));

        IntegerFieldEditor integerFieldEditor = new IntegerFieldEditor(TLCActivator.I_TLC_SNAPSHOT_KEEP_COUNT,
                                                                       "Number of model &snapshots to keep",
                                                                       getFieldEditorParent());
        integerFieldEditor.setValidRange(0, Integer.MAX_VALUE);
        addField(integerFieldEditor);
        
        // addField(new BooleanFieldEditor(ITLCPreferenceConstants.I_TLC_DELETE_PREVIOUS_FILES,
        // "&Automatically delete unused data from previous model run", getFieldEditorParent()));
        addField(new IntegerFieldEditor(ITLCPreferenceConstants.I_TLC_MAXIMUM_HEAP_SIZE_DEFAULT,
                "Maximum JVM Heap Size default in % of physical system memory", getFieldEditorParent()));
        addField(new IntegerFieldEditor(ITLCPreferenceConstants.I_TLC_AUTO_LOCK_MODEL_TIME, "TLC run auto-lock time (in minutes)",
                getFieldEditorParent()));
		
        integerFieldEditor = new IntegerFieldEditor(ITLCPreferenceConstants.I_TLC_TRACE_MAX_SHOW_ERRORS,
				"Default number of states shown in error traces", getFieldEditorParent());
		integerFieldEditor.setValidRange(1, Integer.MAX_VALUE);
		addField(integerFieldEditor);
    }

    public void init(IWorkbench workbench)
    {

    }
}
