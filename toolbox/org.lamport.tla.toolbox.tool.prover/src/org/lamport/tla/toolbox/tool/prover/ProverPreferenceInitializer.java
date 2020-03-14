package org.lamport.tla.toolbox.tool.prover;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.dialog.LaunchProverDialog;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ColorPredicate;
import org.lamport.tla.toolbox.tool.prover.ui.preference.AdditionalPreferencesPage;
import org.lamport.tla.toolbox.tool.prover.ui.preference.ColorPredicatePreferencePage;
import org.lamport.tla.toolbox.tool.prover.ui.preference.MainProverPreferencePage;

/**
 * This class can be used to set default preferences for any preference
 * values that are stored in the preference store for this plugin. This
 * preference store is the one returned by ProverUIActivator.getDefault().getPreferenceStore().
 * 
 * @author Daniel Ricketts
 *
 */
public class ProverPreferenceInitializer extends AbstractPreferenceInitializer
{

    public void initializeDefaultPreferences()
    {
        IPreferenceStore store = ProverUIActivator.getDefault().getPreferenceStore();

        /*
         * Set the default values for the general prover launching
         * dialog.
         */
        store.setDefault(LaunchProverDialog.TOOLBOX_MODE_KEY, true);
        store.setDefault(LaunchProverDialog.EXTRA_OPTIONS_KEY, "");
        store.setDefault(LaunchProverDialog.PARANOID_KEY, false);
        store.setDefault(LaunchProverDialog.ISATOOL_KEY, true);
        store.setDefault(LaunchProverDialog.STATUS_CHECK_KEY, false);
        store.setDefault(LaunchProverDialog.ISACHECK_KEY, false);
        store.setDefault(LaunchProverDialog.NOISA_KEY, false);
        store.setDefault(LaunchProverDialog.FP_NORMAL_KEY, true);
        store.setDefault(LaunchProverDialog.FP_FORGET_ALL_KEY, false);
        store.setDefault(LaunchProverDialog.FP_FORGET_CURRENT_KEY, false);
        store.setDefault(MainProverPreferencePage.EXECUTABLE_LOCATION_KEY, "");
        store.setDefault(MainProverPreferencePage.NUM_THREADS_KEY, "");
        store.setDefault(MainProverPreferencePage.SOLVER_KEY, "");
        store.setDefault(MainProverPreferencePage.SAFEFP_KEY, false);
        
        /*
         * The following sets the default color predicates for the colors. First argument
         * is the key for each predicate for the logical color, and the second argument is
         * the predicate string (not the macro name).
         */
        store.setDefault(ColorPredicatePreferencePage.getColorPredPrefName(1), ColorPredicate.PREDICATE_NONE);
        store.setDefault(ColorPredicatePreferencePage.getColorPredPrefName(2), ColorPredicate.PREDICATE_NONE);
        store.setDefault(ColorPredicatePreferencePage.getColorPredPrefName(3), ColorPredicate.PREDICATE_BEING_PROVED);
        store.setDefault(ColorPredicatePreferencePage.getColorPredPrefName(4), ColorPredicate.PREDICATE_STOPPED);
        store.setDefault(ColorPredicatePreferencePage.getColorPredPrefName(5), ColorPredicate.PREDICATE_FAILED);
        store.setDefault(ColorPredicatePreferencePage.getColorPredPrefName(6), ColorPredicate.PREDICATE_PROVED);
        store.setDefault(ColorPredicatePreferencePage.getColorPredPrefName(7), ColorPredicate.PREDICATE_PROVED_OR_OMITTED);
        store.setDefault(ColorPredicatePreferencePage.getColorPredPrefName(8), ColorPredicate.PREDICATE_PROVED_OR_OMITTED_OR_MISSING);
        store.setDefault(ColorPredicatePreferencePage.getColorPredPrefName(9), ColorPredicate.PREDICATE_NONE);
        store.setDefault(ColorPredicatePreferencePage.getColorPredPrefName(10), ColorPredicate.PREDICATE_NONE);
        store.setDefault(ColorPredicatePreferencePage.getColorPredPrefName(11), ColorPredicate.PREDICATE_NONE);
        store.setDefault(ColorPredicatePreferencePage.getColorPredPrefName(12), ColorPredicate.PREDICATE_NONE);
     
        
       /*
        * Set the defaults for the user-specified color predicates
        */
        for (int i = 0; i < AdditionalPreferencesPage.USER_DEFINED_PREDICATE.length; i++) {
            store.setDefault(AdditionalPreferencesPage.USER_DEFINED_PREDICATE[i], "some");
        }     
    }

}
