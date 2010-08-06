/**
 * 
 */
package org.lamport.tla.toolbox.tool.prover.ui.preference;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.editors.text.EditorsUI;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;

/**
 * @author lamport
 *
 */
public class ProverSecondPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage
{

    /*
     * The names of the preferences for the user-defined predicates.
     */
    public static final String[] USER_DEFINED_PREDICATE = {"UserDefinedPredicateA", "UserDefinedPredicateB", "UserDefinedPredicateC", "UserDefinedPredicateC"};
    public static final String[] UPPER_CASE_LETTERS = {"A", "B", "C", "D", "E", "F"};
    
    public ProverSecondPreferencePage()
    {
        super(GRID);
        setPreferenceStore(ProverUIActivator.getDefault().getPreferenceStore());
        setDescription("User-Defined Color Precicates");
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.preference.FieldEditorPreferencePage#createFieldEditors()
     */
    protected void createFieldEditors()
    {
        System.out.println("adding Test PReference Field");
        for (int i = 0; i < USER_DEFINED_PREDICATE.length; i++) {
            addField(new ColorPredicateFieldEditor(USER_DEFINED_PREDICATE[i], UPPER_CASE_LETTERS[i], getFieldEditorParent()));
        }
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
     */
    public void init(IWorkbench workbench)
    {
        // TODO Auto-generated method stub

    }

}
