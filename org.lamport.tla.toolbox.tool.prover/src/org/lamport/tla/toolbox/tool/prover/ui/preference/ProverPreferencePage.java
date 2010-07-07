package org.lamport.tla.toolbox.tool.prover.ui.preference;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
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
 * @author Daniel Ricketts
 *
 */
public class ProverPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage
{

    /**
     * The number of logical status colors for proof steps.
     */
    public static final int NUM_STATUS_COLORS = 12;

    public ProverPreferencePage()
    {
        super(GRID);
        setPreferenceStore(EditorsUI.getPreferenceStore());
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
            addField(new ColorFieldEditor(getColorPrefName(i), "Color " + i, getFieldEditorParent()));
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
     * in the preference store.
     * 
     * Implementation note : The name returned
     * here must equal the name used for the colorPreferenceKey
     * field of the org.eclipse.ui.editors.markerAnnotationSpecification
     * extension for the marker corresponding to colorNum.
     * 
     * @param colorNum
     * @return
     */
    public static final String getColorPrefName(int colorNum)
    {

        return "stepStatusColor" + colorNum;

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

}
