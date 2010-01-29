package org.lamport.tla.toolbox.tool.tlc.ui.util;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.widgets.Control;

/**
 * This should be used by editors or views that need to update the font of controls
 * when a user changes a font preference.
 * 
 * The class should be instantiated with an array of controls whose font should be updated
 * with the font named fontName. The font name may be found in the plug-in if the font
 * definition is declared in that way or in the name of the field in a preference page
 * if the font preference is added that way.
 * 
 * This should be added as a listener to {@link JFaceResources#getFontRegistry()}.
 * 
 * @author Daniel Ricketts
 *
 */
public class FontPreferenceChangeListener implements IPropertyChangeListener
{
    private Control[] controls;
    private String preferenceName;

    /**
     * Constructor.
     * 
     * @param controls array of controls whose font should be set when the preference corresponding to preferenceName is changed
     * @param fontName name of the font that the controls to which the controls should be set
     */
    public FontPreferenceChangeListener(Control[] controls, String fontName)
    {
        this.controls = controls;
        this.preferenceName = fontName;
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
