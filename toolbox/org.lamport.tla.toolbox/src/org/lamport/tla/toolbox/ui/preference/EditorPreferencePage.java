/**
 * 
 */
package org.lamport.tla.toolbox.ui.preference;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.jface.preference.RadioGroupFieldEditor;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;

/**
 * @author lamport
 */
public class EditorPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage
{

    public static final String EDITOR_RIGHT_MARGIN = "editorRightMargin";
    public static final int EDITOR_RIGHT_MARGIN_DEFAULT = 77;
    
    public static final String EDITOR_ADD_MODIFICATION_HISTORY = "editorAddModificationHistory";
    public static final boolean EDITOR_ADD_MODIFICATION_HISTORY_DEFAULT = true;

    public static final String CLEAR_DECLARATION_USE_MARKERS_ON_PARSE = "removeDeclarationUseMarkersOnParse";
    public static final boolean CLEAR_DECLARATION_USE_MARKERS_ON_PARSE_DEFAULT = true;

    // The following added 26 July 2013 for Renumber proof command options.
    public static final String RENUMBER_KEY = "renumber_proof_option" ;
    public static final String ALL_NAMES = "renumber_proof_all" ;
    public static final String FIRST_DIGIT = "renumber_proof_first_digit" ;
    public static final String SOME_DIGIT = "renumber_proof_some_digit" ;
    public static final String ALL_DIGITS = "renumber_proof_all_digits" ;
    public static final String SAVE_MODULE = "renumber_proof_save" ;
    
    /**
     * 
     */
    public EditorPreferencePage()
    {
        super(GRID);
        setPreferenceStore(Activator.getDefault().getPreferenceStore());
        getPreferenceStore().addPropertyChangeListener(this);
        setDescription("Module Editor preferences");
    }

    /**
     * @param style
     */
    public EditorPreferencePage(int style)
    {
        super(style);
    }

    /**
     * @param title
     * @param style
     */
    public EditorPreferencePage(String title, int style)
    {
        super(title, style);
    }

    /**
     * @param title
     * @param image
     * @param style
     */
    public EditorPreferencePage(String title, ImageDescriptor image, int style)
    {
        super(title, image, style);
    }

    protected Control createContents(Composite parent)
    {
        Control pageControl = super.createContents(parent);
        UIHelper.setHelp(pageControl, IHelpConstants.EDITOR_PREFERENCE_PAGE);
        return pageControl;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.preference.FieldEditorPreferencePage#createFieldEditors()
     */
	protected void createFieldEditors() {
		final IntegerFieldEditor rightMarginEditor = new IntegerFieldEditor(EDITOR_RIGHT_MARGIN,
				"&Module editor right margin", getFieldEditorParent());
        addField(rightMarginEditor);
        rightMarginEditor.setValidRange(20, 200);
        
        addField(new BooleanFieldEditor(CLEAR_DECLARATION_USE_MARKERS_ON_PARSE,
                "&Clear declaration use markers when parsing", getFieldEditorParent()));
        
        addField(new BooleanFieldEditor(EDITOR_ADD_MODIFICATION_HISTORY,
                "&Add a modification history comment to new specs", getFieldEditorParent()));

        
        // Preferences for renumbering.  Added 25 July 2013 by LL
        Label lbl = new Label(getFieldEditorParent(), SWT.NONE);
        GridData gd = new GridData();
        gd.horizontalSpan = 2;
        lbl.setLayoutData(gd);
        
		lbl = new Label(getFieldEditorParent(), SWT.NONE);
		lbl.setText("Renumber Proof Command preferences");
		lbl.setLayoutData(gd);
        
        addField(new RadioGroupFieldEditor(EditorPreferencePage.RENUMBER_KEY, 
        		"Which step names to renumber", 1,
        		new String[][] 
        	      { {"All step names", ALL_NAMES},
        		  {"Names containing  a digit", SOME_DIGIT},
        	      {"Names beginning with a digit", FIRST_DIGIT},
        	      {"Names that are all digits", ALL_DIGITS} },
        		getFieldEditorParent())) ;
        addField(new BooleanFieldEditor(SAVE_MODULE, "&Save module", 
                   getFieldEditorParent()));
        
        
        lbl = new Label(getFieldEditorParent(), SWT.NONE);
        lbl.setLayoutData(gd);
        
        lbl = new Label(getFieldEditorParent(), SWT.NONE);
        lbl.setText("Folding by default preferences");
        lbl.setLayoutData(gd);
        
        addField(new BooleanFieldEditor(IPreferenceConstants.I_FOLDING_BLOCK_COMMENTS,
                "Fold &block comments by default", getFieldEditorParent()));
        
        addField(new BooleanFieldEditor(IPreferenceConstants.I_FOLDING_PCAL_ALGORITHM,
                "Fold &PlusCal algorithm blocks by default", getFieldEditorParent()));
        
        addField(new BooleanFieldEditor(IPreferenceConstants.I_FOLDING_PCAL_TRANSLATED,
                "Fold &translated &PlusCal algorithm TLA+ code by default", getFieldEditorParent()));
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
     */
    public void init(final IWorkbench workbench) { }
}
