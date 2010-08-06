package org.lamport.tla.toolbox.tool.prover.ui.preference;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.layout.GridLayout;
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
 * There is also a slight hack involved in laying out the field editors as we want them.
 * Check out {@link #adjustGridLayout()} to read more about this.  This hack works only
 * because there are no other preferences besides the 12 color-predicate ones.  If we
 * want to put other preferences on the page, the obvious thing to do is to put the
 * color-predicate preferences inside a Composite that is formatted appropriately.
 * Experimentation shows that this doesn't work in the obvious way.  Instead, each
 * field editor has to be put inside a separate composite inside the multi-column
 * composite.  The following code seems to work:
 *     protected void createFieldEditors()
 *    {
 *        Composite composite = new Composite(getFieldEditorParent(), SWT.NONE);
 *        GridLayout layout = new GridLayout();
 *        layout.numColumns = 4;
 *        layout.horizontalSpacing = 20;
 *        composite.setLayout(layout);
 *
 *        for (int i = 1; i <= NUM_STATUS_COLORS; i++)
 *        {
 *            Composite c = new Composite(composite, SWT.NONE);
 *            addField(new ColorFieldEditor(getMainColorPrefName(i), "Color "  + i + (i>9?"":"  "), c));
 *            c = new Composite(composite, SWT.NONE);
 *            addField(new ComboFieldEditor(getColorPredPrefName(i), "Predicate", ColorPredicate.PREDEFINED_MACROS, c));
 *            c = new Composite(composite, SWT.NONE);
 *            addField(new BooleanFieldEditor(getLeafSideBarPrefName(i), "Show Leaf Steps in Side Bar", c));
 *            c = new Composite(composite, SWT.NONE);
 *            addField(new BooleanFieldEditor(getAppliesToLeafPrefName(i), "Applies to Leaf Steps Only", c));
 *        }
 *    }
 *
 * However, the documentation warns that getFieldEditorParent() should be called 
 * separately for each field.  This doesn't seem to be necessary for a GRID layout,
 * but Dan & LL decided not to risk it and instead to put other preferences on a
 * separate page.
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
     * When the color preference is changed for the key which is bound to the color
     * field editors for this page, this method sets the value for the partner key
     * to be the same.
     * See the documentation for this class to read more about this.
     */
    public void propertyChange(PropertyChangeEvent event)
    {
        if (event.getProperty().contains(COLOR_PREF_KEY_PREFIX) && event.getProperty().endsWith("A"))
        {
            /*
             * Setting preferences is a bit strange. The strangeness occurs
             * when calling IPreferenceStore.setValue(name,value) when the value
             * is equal to the default value for that name.
             * 
             * When the value is NOT equal to the default value and is not equal to the old
             * value, the preference store sets name to map to the new value and
             * informs all interested listeners of the change. I believe that
             * the eclipse text editors are among these interested listeners. This
             * is how they update the colors used for annotations.
             * 
             * However, when the value is equal to the default value for name, the preference
             * store removes the preference mapping for name (I assume the defaults are stored
             * somewhere else in the store) and informs all listeners that the preference
             * for name has been removed and does not inform them that it has been set to
             * the default value. The method comments for setValue() indicate that the correct
             * way to restore default preference values is to call store.setToDefault(). Thus,
             * it appears that we have to check whether the value we are setting is the default
             * value. If it is, we use setToDefault(). If it isn't, we use setValue().
             * 
             * Note that this strange behavior only seems to be for ScopedPreferenceStore, which
             * is the type of preference store used for this page.
             */
            int colorNum = getNumFromMainColorPref(event.getProperty());
            IPreferenceStore store = getPreferenceStore();
            String partnerPrefName = getPartnerColorPrefName(colorNum);
            /*
             * You might be wondering why in the following I did not use event.getNewValue() to
             * retrieve the new color value. It turns out that sometimes
             * that method returns an object of type RGB and sometimes a String.
             * For all I know, it could return another type entirely in certain
             * situations. Thus, it seems that the best thing is to get the value
             * directly from the preference store instead of from the event. The preference
             * store keeps the value of a color as a String, so the type returned is a string
             * and the type to set for the partner preference name is also a String.
             */
            String newValue = getPreferenceStore().getString(event.getProperty());
            if (store.getDefaultString(partnerPrefName).equals(newValue))
            {
                store.setToDefault(partnerPrefName);
            } else
            {
                getPreferenceStore().setValue(partnerPrefName, newValue);
            }
        }

        super.propertyChange(event);
    }

    /**
     * This overrides the method in {@link FieldEditorPreferencePage} in order
     * to place multiple field editors on a single line. The superclass implementation
     * of this method puts one field editor per line of preference page. However,
     * we want to put all the field editors for each logical color on a single
     * line so that the page is a little more compact.
     */
    protected void adjustGridLayout()
    {
        /*
         * All that needs to be done is adjusting the number of columns of the layout
         * of widgets on the page. Each logical color seems to have 6 widgets:
         * 
         * 1.) Color label
         * 2.) Color selection widget
         * 3.) Predicate label
         * 4.) Predicate selection widget
         * 5.) Show leaf steps in side bar (the label and check box are somehow one widget)
         * 6.) Applies to leaf steps (the label and check box are somehow one widget)
         * 
         * If the field editors change on this page, this method will have to change.
         */
        ((GridLayout) getFieldEditorParent().getLayout()).numColumns = 6;
    }
}
