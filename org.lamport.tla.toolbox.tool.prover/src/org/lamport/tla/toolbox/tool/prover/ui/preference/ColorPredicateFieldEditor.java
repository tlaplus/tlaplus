/**
 * 
 */
package org.lamport.tla.toolbox.tool.prover.ui.preference;

import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.widgets.Composite;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ColorPredicate;

/**
 * @author lamport
 *
 */
public class ColorPredicateFieldEditor extends StringFieldEditor
{
    public ColorPredicateFieldEditor(String name, String label, Composite parent)
    {
        super(name, label, StringFieldEditor.UNLIMITED, StringFieldEditor.VALIDATE_ON_KEY_STROKE , parent);
    }

    public boolean doCheckState()
    {
        String value = this.getStringValue();
        value = value.trim();
        if (value.startsWith("leaf"))
        {

//            showErrorMessage("should not begin with `leaf'");
            return false;
        }
        try
        {
            new ColorPredicate(value);
        } catch (Exception e)
        {
            return false;
        }
        return true;
    }

}
