package org.lamport.tla.toolbox.util;

import java.util.Vector;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.widgets.Control;

/**
 * This should be used by editors or views that need to update the font of controls
 * when a user changes a font preference.
 * 
 * The class should be instantiated with a list of controls whose font should be updated
 * with the font named fontName. The font name may be found in the plug-in if the font
 * definition is declared in that way or in the name of the field in a preference page
 * if the font preference is added that way.
 * 
 * Additional controls can be added to the list of controls to be updated by calling
 * {@link FontPreferenceChangeListener#addControl(Control)}.
 * 
 * This should be added as a listener to {@link JFaceResources#getFontRegistry()}.
 * 
 * @author Daniel Ricketts
 *
 */
public class FontPreferenceChangeListener implements IPropertyChangeListener
{
    private Vector controls;
    private String preferenceName;

    /**
     * Constructor.
     * 
     * @param controls list of controls whose font should be set when the preference corresponding to
     * preferenceName is changed. If null, then no controls will be notified until added using addControl().
     * @param fontName name of the font that the controls to which the controls should be set
     */
    public FontPreferenceChangeListener(Vector controls, String fontName)
    {
        if (controls != null)
        {
            this.controls = controls;
        } else
        {
            this.controls = new Vector();
        }
        this.preferenceName = fontName;
    }

    public void propertyChange(PropertyChangeEvent event)
    {
        if (event.getProperty().equals(preferenceName))
        {
            for (int i = 0; i < controls.size(); i++)
            {
                ((Control) controls.get(i)).setFont(JFaceResources.getFont(preferenceName));
            }
        }
    }

    /**
     * Adds a control to the set of controls whose font should be
     * set when the preference corresponding to preferenceName is changed
     * 
     * @param control
     */
    public void addControl(Control control)
    {
        controls.add(control);
    }

}
