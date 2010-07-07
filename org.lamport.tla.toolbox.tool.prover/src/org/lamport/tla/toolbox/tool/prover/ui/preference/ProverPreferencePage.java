package org.lamport.tla.toolbox.tool.prover.ui.preference;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.editors.text.EditorsUI;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ColorPredicate;

/**
 * This class represents the prover preference page that
 * is contributed to the Preferences dialog. By 
 * subclassing <samp>FieldEditorPreferencePage</samp>, we
 * can use the field support built into JFace that allows
 * us to create a page that is small and knows how to 
 * save, restore and apply itself.
 * <p>
 * This page is used to modify preferences only. They
 * are stored in the preference store returned by
 * EditorUI.getPreferenceStore(). That way, preferences can
 * be accessed directly via the preference store.
 * 
 * We use the preference store from EditorUI.getPreferenceStore() because
 * that is where the preferences for annotation colors are stored by
 * eclipse, and we use marker annotations to show step status colors
 * in the editor.
 * 
 * There is some hackery involved in setting the color preference values.
 * For each logical color that appears on this preference page, there are
 * two marker types and thus two annotation types. One annotation type
 * corresponds to leaf steps and one to non-leaf steps. Each annotation type
 * has a key in the preference store that maps to that annotation's color.
 * Both annotation types for a given logical color should always be bound to the
 * same physical color. Thus, when the user changes the value of a logical
 * color, the two color preference keys for the two annotation types must both
 * map to the new physical color.
 * 
 * The original implementation used the same color preference key for both
 * annotation types. However, this does not seem to work. It appears that when
 * the physical color preference is changed for a given logical color, the editor
 * only recognizes the change to the color for one of the annotation types even though
 * the color has changed for both annotation types because they both have the same
 * color preference key.
 * 
 * The solution is the following. Use different color preference keys for two
 * annotation types corresponding to a given logical color. Only one of the keys
 * can be bound to the color field editor on the preference page. This page listens
 * for changes to the value of that key. When the value is changed, it sets the value
 * of its partner key to be the same. This is done in the method {@link #propertyChange(PropertyChangeEvent)}.
 * 
 * @author Daniel Ricketts
 *
 */
public class ProverPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage
{

    /**
     * The number of logical status colors for proof steps.
     */
    public static final int NUM_STATUS_COLORS = 12;

    /**
     * The prefix for the keys used for color preferences.
     */
    public static final String COLOR_PREF_KEY_PREFIX = "stepStatusColor";

    public ProverPreferencePage()
    {
        super(GRID);
        setPreferenceStore(EditorsUI.getPreferenceStore());
        getPreferenceStore().addPropertyChangeListener(this);
        setDescription("TLAPS preferences");
    }

    /**
     * Creates the field editors. Field editors are abstractions of
     * the common GUI blocks needed to manipulate various types
     * of preferences. Each field editor knows how to save and
     * restore itself.
     */
    protected void createFieldEditors()
    {

        for (int i = 1; i <= NUM_STATUS_COLORS; i++)
        {
            addField(new ColorFieldEditor(getMainColorPrefName(i), "Color " + i, getFieldEditorParent()));
            addField(new ComboFieldEditor(getColorPredPrefName(i), "Predicate", ColorPredicate.PREDEFINED_MACROS,
                    getFieldEditorParent()));
            addField(new BooleanFieldEditor(getLeafSideBarPrefName(i), "Show Leaf Steps in Side Bar",
                    getFieldEditorParent()));
            addField(new BooleanFieldEditor(getAppliesToLeafPrefName(i), "Applies to Leaf Steps Only",
                    getFieldEditorParent()));

        }

    }

    /**
     * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
     */
    public void init(IWorkbench workbench)
    {
    }

    /**
     * Returns the preference name for the color value for logical
     * color colorNum. This is the name used to store the preference
     * in the preference store. This is the name used for the color field editor.
     * There is another "partner" key that should also be bound to the same color.
     * See the class documentation for an explanation.
     * 
     * Implementation note : The name returned
     * here must equal the name used for the colorPreferenceKey
     * field of the org.eclipse.ui.editors.markerAnnotationSpecification
     * extension for the non-leaf marker corresponding to colorNum.
     * 
     * @param colorNum
     * @return
     */
    public static final String getMainColorPrefName(int colorNum)
    {

        return COLOR_PREF_KEY_PREFIX + colorNum + "A";

    }

    /**
     * Returns the preference name for the color value for logical
     * color colorNum. This is the name used to store the preference
     * in the preference store. This is NOT the name used for the color field editor.
     * This is the partner key of the key used for the color field editor.
     * See the class documentation for an explanation.
     * 
     * Implementation note : The name returned
     * here must equal the name used for the colorPreferenceKey
     * field of the org.eclipse.ui.editors.markerAnnotationSpecification
     * extension for the leaf marker corresponding to colorNum.
     * 
     * @param colorNum
     * @return
     */
    public static final String getPartnerColorPrefName(int colorNum)
    {
        return COLOR_PREF_KEY_PREFIX + colorNum + "B";
    }

    /**
     * Gets the number of the color given the color preference
     * key for that color. Note that this is the color preference
     * key for the color field editor. These keys are produced using the
     * method {@link #getMainColorPrefName(int)}.
     * There is another "partner" key that should also be bound to the same color.
     * See the class documentation for an explanation.
     * 
     * @param key
     * @return
     */
    public static final int getNumFromMainColorPref(String key)
    {
        // the number is from the end of the prefix to the second to last character
        // the last character is "A" or "B".
        return Integer.parseInt(key.substring(COLOR_PREF_KEY_PREFIX.length(), key.length() - 1));
    }

    /**
     * Returns the preference name for the color predicate
     * for logical color colorNum. This is the name used to store
     * the preference in the preference store.
     * 
     */
    public static final String getColorPredPrefName(int colorNum)
    {

        return "stepStatusColor" + colorNum + "predicate";

    }

    /**
     * Returns the preference name for the boolean preference
     * of showing leaf markers in the side bar. That is, if selected
     * whenever the physical color corresponding to colorNum is shown
     * in the editor on a leaf step, it will appear in the side bar as well.
     * This is the name used to store the preference in the preference store.
     * 
     * @param colorNum
     * @return
     */
    public static final String getLeafSideBarPrefName(int colorNum)
    {

        return "stepStatusOverview" + colorNum + "B";

    }

    /**
     * Returns the preference name for the boolean preference of whether the
     * color applies only to leaf steps. This is the name used to store the preference
     * in the preference store.
     * 
     * @param colorNum
     * @return
     */
    public static final String getAppliesToLeafPrefName(int colorNum)
    {
        return "appliesToLeafOnly" + colorNum;
    }

    /**
     * This method makes sure pairs of annotation types corresponding
     * to a given logical color are always bound to the same physical color.
     * See the documentation for this class to read more about this.
     */
    public void propertyChange(PropertyChangeEvent event)
    {
        if (event.getProperty().contains(COLOR_PREF_KEY_PREFIX) && event.getProperty().endsWith("A"))
        {
            int colorNum = getNumFromMainColorPref(event.getProperty());
            PreferenceConverter.setValue(getPreferenceStore(), getPartnerColorPrefName(colorNum), (RGB) event
                    .getNewValue());
        }

        super.propertyChange(event);
    }
}
