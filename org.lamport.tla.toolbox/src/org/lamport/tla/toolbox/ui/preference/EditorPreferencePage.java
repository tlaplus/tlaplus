/**
 * 
 */
package org.lamport.tla.toolbox.ui.preference;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * @author lamport
 *
 */
public class EditorPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage
{

    public static final String EDITOR_RIGHT_MARGIN = "editorRightMargin";
    public static final int EDITOR_RIGHT_MARGIN_DEFAULT = 77;
    
    public static final String CLEAR_DECLARATION_USE_MARKERS_ON_PARSE = "removeDeclarationUseMarkersOnParse";
    public static final boolean CLEAR_DECLARATION_USE_MARKERS_ON_PARSE_DEFAULT = true;
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
        // TODO Auto-generated constructor stub
    }

    /**
     * @param title
     * @param style
     */
    public EditorPreferencePage(String title, int style)
    {
        super(title, style);
        // TODO Auto-generated constructor stub
    }

    /**
     * @param title
     * @param image
     * @param style
     */
    public EditorPreferencePage(String title, ImageDescriptor image, int style)
    {
        super(title, image, style);
        // TODO Auto-generated constructor stub
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
    protected void createFieldEditors()
    {   IntegerFieldEditor rightMarginEditor = 
            new IntegerFieldEditor(EDITOR_RIGHT_MARGIN, "&Module editor right margin", 
                   getFieldEditorParent());
        addField(rightMarginEditor);
        rightMarginEditor.setValidRange(20, 200);
        
        addField(new BooleanFieldEditor(CLEAR_DECLARATION_USE_MARKERS_ON_PARSE,
                "&Clear declaration use markers when parsing", getFieldEditorParent()));
    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
     */
    public void init(IWorkbench workbench)
    {
        // TODO Auto-generated method stub

    }

}
