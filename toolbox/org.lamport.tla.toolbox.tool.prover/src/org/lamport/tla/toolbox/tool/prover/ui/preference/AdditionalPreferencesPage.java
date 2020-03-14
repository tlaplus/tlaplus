/**
 * 
 */
package org.lamport.tla.toolbox.tool.prover.ui.preference;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;

/**
 * @author lamport
 */
public class AdditionalPreferencesPage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
    /*
     * The names of the preferences for the user-defined predicates.
     */
    public static final String[] USER_DEFINED_PREDICATE = { "UserDefinedPredicateA", "UserDefinedPredicateB",
            "UserDefinedPredicateC", "UserDefinedPredicateD", "UserDefinedPredicateE", "UserDefinedPredicateF"};
    public static final String[] UPPER_CASE_LETTERS = { "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L" };

	public AdditionalPreferencesPage() {
        super(GRID);
        setPreferenceStore(ProverUIActivator.getDefault().getPreferenceStore());
        setDescription("User-Defined Color Predicates");
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.preference.FieldEditorPreferencePage#createFieldEditors()
     */
	protected void createFieldEditors() {
        // To change the number of user-defined predicates, look up all uses of
        // USER_DEFINED_PREDICATE and USER_DEFINED.
        for (int i = 0; i < USER_DEFINED_PREDICATE.length; i++)
        {
            addField(new ColorPredicateFieldEditor(USER_DEFINED_PREDICATE[i],
                    "     Predicate " + UPPER_CASE_LETTERS[i], getFieldEditorParent()));
        }
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
     */
	public void init(IWorkbench workbench) { }
}
