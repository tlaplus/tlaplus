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

/**
 * @author lamport
 *
 */
public class ProverSecondPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage
{

    public ProverSecondPreferencePage()
    {
        super(GRID);
        setPreferenceStore(EditorsUI.getPreferenceStore());
        setDescription("Color Precicates");
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.preference.FieldEditorPreferencePage#createFieldEditors()
     */
    protected void createFieldEditors()
    {
        System.out.println("adding Test PReference Field");
        addField(new ColorPredicateFieldEditor("TestPreferenceName", "Label", getFieldEditorParent()));

    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
     */
    public void init(IWorkbench workbench)
    {
        // TODO Auto-generated method stub

    }

}
