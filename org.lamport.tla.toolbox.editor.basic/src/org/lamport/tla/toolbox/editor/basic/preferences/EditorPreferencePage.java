/**
 * 
 */
package org.lamport.tla.toolbox.editor.basic.preferences;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.lamport.tla.toolbox.editor.basic.TLAEditorActivator;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;
//import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * @author lamport
 *
 */
public class EditorPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage
{

    public static final String EDITOR_RIGHT_MARGIN = "editorRightMargin";
    public static final int EDITOR_RIGHT_MARGIN_DEFAULT = 77;
    /**
     * 
     */
    public EditorPreferencePage()
    {
        super(GRID);
        setPreferenceStore(TLAEditorActivator.getDefault().getPreferenceStore());
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

    }

    /* (non-Javadoc)
     * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
     */
    public void init(IWorkbench workbench)
    {
        // TODO Auto-generated method stub

    }

}
