/**
 * 
 */
package org.lamport.tla.toolbox.tool.prover.ui.preference;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
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
    public static final String[] USER_DEFINED_PREDICATE = { "UserDefinedPredicateA", "UserDefinedPredicateB",
            "UserDefinedPredicateC", "UserDefinedPredicateD", "UserDefinedPredicateE", "UserDefinedPredicateF"};
    public static final String[] UPPER_CASE_LETTERS = { "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L" };
    public static final String NUM_THREADS_KEY = "num_threads";
    public static final String SOLVER_KEY = "solver";
    public static final String SAFEFP_KEY = "safefp";

    public ProverSecondPreferencePage()
    {
        super(GRID);
        setPreferenceStore(ProverUIActivator.getDefault().getPreferenceStore());
        setDescription("User-Defined Color Predicates");
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.preference.FieldEditorPreferencePage#createFieldEditors()
     */
    protected void createFieldEditors()
    {
        // To change the number of user-defined predicates, look up all uses of
        // USER_DEFINED_PREDICATE and USER_DEFINED.
        for (int i = 0; i < USER_DEFINED_PREDICATE.length; i++)
        {
            addField(new ColorPredicateFieldEditor(USER_DEFINED_PREDICATE[i],
                    "     Predicate " + UPPER_CASE_LETTERS[i], getFieldEditorParent()));
        }

        /*
         * Add some space.  We seem to need to add two labels to avoid screwing
         * up the formatting.
         */

        new Label(getFieldEditorParent(), SWT.NONE);
        new Label(getFieldEditorParent(), SWT.NONE);

        addField(new ThreadsFieldEditor(NUM_THREADS_KEY, "Num. of Threads", getFieldEditorParent()));
        addField(new SolverFieldEditor(SOLVER_KEY, "SMT Solver", getFieldEditorParent()));
        // Label cpLabel = new Label(getFieldEditorParent(), SWT.NONE);
        // cpLabel.setText("Do not trust previous results from earlier versions of provers?");
        // GridData gd = new GridData();
        // gd.horizontalSpan = 2;
        // cpLabel.setLayoutData(gd);

        new Label(getFieldEditorParent(), SWT.NONE);
        new Label(getFieldEditorParent(), SWT.NONE);

        addField(new BooleanFieldEditor(SAFEFP_KEY, "Do not trust previous results from earlier versions of provers.",
                getFieldEditorParent()));

    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
     */
    public void init(IWorkbench workbench)
    {
        // TODO Auto-generated method stub

    }

    public class ThreadsFieldEditor extends StringFieldEditor
    {
        public ThreadsFieldEditor(String arg0, String arg1, Composite arg2)
        {
            super(arg0, arg1, arg2);
        }

        public boolean doCheckState()
        {
            String value = this.getStringValue();
            value = value.trim();
            if (value.length() == 0)
            {
                return true;
            }
            try
            {
                int numThreads = Integer.parseInt(value);
                return numThreads > 0;
            } catch (NumberFormatException e)
            {
                return false;
            }
        }
    }

    public class SolverFieldEditor extends StringFieldEditor

    {
        public SolverFieldEditor(String arg0, String arg1, Composite arg2)
        {
            super(arg0, arg1, arg2);
        }

        public boolean doCheckState()
        {
            String value = this.getStringValue();
            return value.indexOf('"') == -1;
        }
    }

}
