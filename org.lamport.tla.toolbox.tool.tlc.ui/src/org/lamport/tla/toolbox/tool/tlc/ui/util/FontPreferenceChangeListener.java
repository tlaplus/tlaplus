package org.lamport.tla.toolbox.tool.tlc.ui.util;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.widgets.Control;

public class FontPreferenceChangeListener implements IPropertyChangeListener
{
    private Control[] controls;
    private String preferenceName;

    /**
     * 
     * @param controls array of controls whose font should be set when the preference corresponding to preferenceName is changed
     * @param preferenceName name of the font preference that the controls to which the controls should be set
     * @param preferenceStore the preference store that holds the font preference
     */
    public FontPreferenceChangeListener(Control[] controls, String preferenceName)
    {
        this.controls = controls;
        this.preferenceName = preferenceName;
    }

    public void propertyChange(PropertyChangeEvent event)
    {
        if (event.getProperty().equals(preferenceName))
        {
            for (int i = 0; i < controls.length; i++)
            {
                controls[i].setFont(JFaceResources.getFont(preferenceName));
            }
        }
    }

}
