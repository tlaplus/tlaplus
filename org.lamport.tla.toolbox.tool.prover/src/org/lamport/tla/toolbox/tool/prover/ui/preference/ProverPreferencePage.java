package org.lamport.tla.toolbox.tool.prover.ui.preference;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.jface.window.IShellProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.events.VerifyEvent;
import org.eclipse.swt.events.VerifyListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.eclipse.ui.editors.text.EditorsUI;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ColorPredicate;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;
import org.lamport.tla.toolbox.util.UIHelper;

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
        // Using somebody's else PreferenceStore is not a good idea!
        // @see https://bugzilla.tlaplus.net/show_bug.cgi?id=261
        IPreferenceStore store = EditorsUI.getPreferenceStore();
        
        setPreferenceStore(store);
        getPreferenceStore().addPropertyChangeListener(this);
        setDescription("Color Predicates");
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

        /*
         * Because of an Eclipse bug reported at
         *    https://bugs.eclipse.org/bugs/show_bug.cgi?id=279840
         * a ColorFieldEditor doesn't work on the Mac.  For the Mac, we
         * add a dialog for choosing color-predicate colors.  Here we add the
         * button that raises this dialog, which is a MacColorSelectionDialog,
         * where that class is declared below.
         */
        if (ProverHelper.isMac())
        {
            Button macColorButton = new Button(getFieldEditorParent(), SWT.PUSH);
            macColorButton.setText("Set Colors");
            macColorButton.addSelectionListener(new MacColorButtonSelectionListener());
            Label warning = new Label(getFieldEditorParent(), SWT.NONE);
            GridData gd = new GridData();
            gd.horizontalSpan = 5;
            warning.setLayoutData(gd);
            warning.setText("If you have made any changes, click Apply before setting colors.");
            // Label lbl = new Label(getFieldEditorParent(), SWT.NONE);
            // GridData gd = new GridData();
            // gd.horizontalSpan = 5;
            // lbl.setLayoutData(gd);
            // lbl = new Label(getFieldEditorParent(), SWT.NONE);
            // lbl.setText("Set color-predicate colors");
            // lbl.setLayoutData(gd);
            // IPreferenceStore store = EditorsUI.getPreferenceStore();
            // PreferenceConverter.setValue(store, getMainColorPrefName(12), new RGB(255, 0, 0));
            // ...
            // RBG bgColor = PreferenceConverter.getValue(store, "bg");

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

    static class MacColorButtonSelectionListener implements SelectionListener
    {
        public void widgetDefaultSelected(SelectionEvent e)
        {
            /*
             * This never seems to be called.
             */

        }

        public void widgetSelected(SelectionEvent e)
        {
            MacColorSelectionDialog dialog = new MacColorSelectionDialog(UIHelper.getShellProvider());
            dialog.open();
        }

    }

    /**
     * This is a Dialog for choosing color-predicate colors.  Each color's rgb
     * values are specified by 3 Text fields, all on one line, with the line
     * labeled with a Label containing the color number whose background color
     * is the specified color.  These values are initialized to the appropriate
     * values in the preference store.  When the OK button is pressed, the
     * preference store's values are updated appropriately.  
     * 
     * There is one problem.  On the PC, I observe the following behavior.  When 
     * the OK (or Apply) button is pressed on the preference page, the preference store
     * values are set to the colors currently specified by the ColorFieldEditors
     * on that page.  Those colors aren't changed by pressing the Dialog's OK
     * button.  Hence, to avoid the color's the user has just chosen from being
     * replaced by their previous values, the user must hit the Cancel button
     * on the preference page.
     * 
     * Note: It would seem that this problem could be solved by raising this
     * dialog with a button a different preference page.  However, I have observed
     * that if this is done, the color predicate preference page's colors still
     * have their previous values when that page is next raised.  Hitting the 
     * Cancel button on that page then seems to make the page have the right
     * colors the next time it is raised.  Hitting OK reverts the preference
     * store to contain the previous colors.  This makes no sense, because my
     * experience says that the preference page's createFieldEditors() method is 
     * called every time the page is raised, and method sets the ColorFieldEditors'
     * colors from the preference store, which must have been changed because
     * the new colors appear on the proof's markers.  However, we don't
     * expect the actions of Eclipse methods to make sense.  In other circumstances
     * as well, we have observed the Eclipse preference store doing totally
     * inexplicable things.  When using the preference store, one has to just
     * find what works and hope that it also works on other systems.
     * 
     * The other non-obvious thing that the dialog does is to dispose of
     * all Color objects that it creates by calling the dispose() method.
     * On some computers, there is a maximum number of different colors that
     * can be displayed on the screen, and dispose() must be called on a
     * Color object (even after it's not allocated) to free up the resource
     * it occupies.  For that reason, the Colors are kept as fields of the
     * MacColorSelectionDialog object, and that object is passed to the
     * listeners which must dispose of the colors.
     * 
     * @author lamport
     *
     */
    public static class MacColorSelectionDialog extends Dialog
    {
        /*
         * Text[i][1] is the Text area for the green component of color i
         */
        public Text[][] rgbText = new Text[12][];
        /*
         * colorNumber[i] labels color i+1, and color[i] is the Color resource that
         * colors this label.  That resource is disposed() when the dialog is closed.
         */
        public Label[] colorNumber = new Label[12];
        public Color[] color = new Color[12];

        public MacColorSelectionDialog(IShellProvider parentShell)
        {
            super(parentShell);
            setBlockOnOpen(true);
            // this.page = page;
        }

        protected Control createDialogArea(Composite parent)
        {
            Composite topComposite = new Composite(parent, SWT.NONE);
            GridData gd = new GridData();
            topComposite.setLayoutData(gd);
            topComposite.setLayout(new GridLayout(7, false));

            // Using somebody's else PreferenceStore is not a good idea!
        	// Use ProverUIActivator.getDefault().getPreferenceStore() instead.
            // @see https://bugzilla.tlaplus.net/show_bug.cgi?id=261
	        IPreferenceStore store = EditorsUI.getPreferenceStore();
            /*
             * Set up the Text fields and their labels for selecting the colors.
             */
            for (int i = 0; i < 12; i++)
            {
                RGB bgColor = PreferenceConverter.getColor(store, getMainColorPrefName(i + 1));

                colorNumber[i] = new Label(topComposite, SWT.NONE);
                colorNumber[i].setText("Color " + (i + 1));
                color[i] = new Color(null, bgColor);
                colorNumber[i].setBackground(color[i]);

                Label[] rgbLabel = new Label[3];
                rgbText[i] = new Text[3];
                for (int j = 0; j < 3; j++)
                {
                    rgbLabel[j] = new Label(topComposite, SWT.None);
                    rgbText[i][j] = new Text(topComposite, SWT.None);

                }
                /*
                 * I have been unable to set the size of a Text area to an
                 * explicit value.  The setSize method doesn't seem to do
                 * anything.  The Text area seems to size itself so its initial
                 * text just fits.  So, we use the makeAtLeastThreeDigitsWide
                 * method to make the value (which should be between 0 and 255)
                 * contain exactly three digits.
                 */
                rgbText[i][0].setText(makeAtLeastThreeDigitsWide(bgColor.red));
                rgbText[i][1].setText(makeAtLeastThreeDigitsWide(bgColor.green));
                rgbText[i][2].setText(makeAtLeastThreeDigitsWide(bgColor.blue));
                rgbLabel[0].setText("    r:");
                rgbLabel[1].setText("    g:");
                rgbLabel[2].setText("    b:");

                /*
                 * Have to add the VerifyListeners after the Text areas are set to valid
                 * values.
                 */
                for (int j = 0; j < 3; j++)
                {
                    rgbText[i][j].addVerifyListener(new MacColorVerifyListener(this, i, j));
                }
            }
            Label spacer = new Label(topComposite, SWT.NONE);
            GridData spacerData = new GridData();
            spacerData.horizontalSpan = 7;
            spacer.setLayoutData(spacerData);
            Label instructions = new Label(topComposite, SWT.NONE);
            instructions.setLayoutData(spacerData);
            instructions.setText("To change colors, click on OK then click on");
            instructions = new Label(topComposite, SWT.NONE);
            instructions.setLayoutData(spacerData);
            instructions.setText("the Cancel button of the preference page.");
            return topComposite;
        }

        protected void okPressed()
        {
            // Using somebody's else PreferenceStore is not a good idea!
        	// Use ProverUIActivator.getDefault().getPreferenceStore() instead.
            // @see https://bugzilla.tlaplus.net/show_bug.cgi?id=261
	        IPreferenceStore store = EditorsUI.getPreferenceStore();

            for (int i = 0; i < 12; i++)
            {
                int[] newrgb = new int[3];
                for (int j = 0; j < 3; j++)
                {
                    newrgb[j] = Integer.valueOf(rgbText[i][j].getText()).intValue();
                }
                RGB bgColor = PreferenceConverter.getColor(store, getMainColorPrefName(i + 1));
                if (bgColor.red != newrgb[0] || bgColor.green != newrgb[1] || bgColor.blue != newrgb[2])
                {
                    PreferenceConverter.setValue(store, getMainColorPrefName(i + 1), new RGB(newrgb[0], newrgb[1],
                            newrgb[2]));
                }

                this.color[i].dispose();
            }
            super.okPressed();
        }

        protected void cancelPressed()
        {
            for (int i = 0; i < 12; i++)
            {
                this.color[i].dispose();
            }
            super.okPressed();
        }

    }

    public static class MacColorVerifyListener implements VerifyListener
    {
        MacColorSelectionDialog dialog;
        int colorNum;
        int rgbNum;

        public MacColorVerifyListener(MacColorSelectionDialog dialog, int colorNum, int rgbNum)
        {
            super();
            this.dialog = dialog;
            this.colorNum = colorNum;
            this.rgbNum = rgbNum;
        }

        /*
         * (non-Javadoc)
         * This method is called before the change is made to the
         * Text field.  The fields of the VerifyEvent e indicates what the
         * change will be.  Setting e.doit to false prevents the change
         * from occurring.  Setting e.text will change the character(s) being 
         * entered.
         * @see org.eclipse.swt.events.VerifyListener#verifyText(org.eclipse.swt.events.VerifyEvent)
         */
        public void verifyText(VerifyEvent e)
        {
            /*
             * Sets newText to the new value of the field if the keystroke is acted on.
             */
            String oldText = this.dialog.rgbText[colorNum][rgbNum].getText();
            String newText = oldText.substring(0, e.start) + e.text + oldText.substring(e.end);
            /*
             * Since the Text field is only 3 characters wide, we don't want the contents
             * to have more than 3 characters.  So, we abort the action if it would make
             * the field have more than 3 characters.  I'd like to just remove leading zeros
             * if that would bring the text down to 3 characters, but that doesn't seem to
             * be possible except in certain circumstances, which I haven't bothered to
             * handle.
             */
            if (newText.length() > 3)
            {
                e.doit = false;
                return;
            }
            int redVal;
            if (newText.equals(""))
            {
                redVal = 0;
            } else
            {
                try
                {
                    redVal = Integer.valueOf(newText).intValue();

                } catch (Exception e2)
                {
                    e.doit = false;
                    return;
                }
            }
            if (redVal > 255 || redVal < 0)
            {
                e.doit = false;
                return;
            }

            // TLCActivator.getDefault().logDebug("oldText = " + this.dialog.rgbText[0].getText() + " , newText = `" + newText + "'");
            int[] rgbVals = new int[3];

            for (int i = 0; i < 3; i++)
            {
                if (i == rgbNum)
                {
                    rgbVals[i] = redVal;
                } else
                {
                    rgbVals[i] = Integer.valueOf(this.dialog.rgbText[colorNum][i].getText()).intValue();
                }
            }
            try
            {
                RGB rgb = new RGB(rgbVals[0], rgbVals[1], rgbVals[2]);

                dialog.color[colorNum] = new Color(null, rgb);
                dialog.colorNumber[colorNum].setBackground(dialog.color[colorNum]);
            } catch (IllegalArgumentException ee)
            {
                // TODO: handle exception
            }
        }

    }

    public static String makeAtLeastThreeDigitsWide(int value)
    {
        String result = "";
        if (value < 100)
        {
            result = result + "0";
            if (value < 10)
            {
                result = result + "0";
            }
        }
        return result + value;
    }
}
