package org.lamport.tla.toolbox.tool.tla2tex.preference;

import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.widgets.Composite;

/**
 * This field editor overrides some methods of StringFieldEditor
 * to only allow real numbers in the given range to be entered and stored.
 * 
 * @author Daniel Ricketts
 * @version $Id$
 */
public class DoubleFieldEditor extends StringFieldEditor
{

    private double minVal;
    private double maxVal;

    public DoubleFieldEditor(String name, String labelText, Composite parent, double min, double max)
    {
        super(name, labelText, parent);
        minVal = min;
        maxVal = max;
    }

    protected boolean checkState()
    {
        String errorMessage = "Enter a real number between " + minVal + " and " + maxVal + ".";
        try
        {
            String text = getTextControl().getText();
            if (text.endsWith("d") || text.endsWith("f") || text.contains("e"))
            {
                showErrorMessage(errorMessage);
                return false;
            }
            double value = Double.parseDouble(text);
            clearErrorMessage();
            return value >= minVal && value <= maxVal;
        } catch (NumberFormatException e)
        {
            showErrorMessage(errorMessage);
            return false;
        }

    }

    protected void doStore()
    {
        try
        {
            getPreferenceStore().setValue(getPreferenceName(), Double.parseDouble(getTextControl().getText()));
        } catch (NumberFormatException e)
        {
            getPreferenceStore().setValue(getPreferenceName(),
                    getPreferenceStore().getDefaultDouble(getPreferenceName()));
        }
    }

}
