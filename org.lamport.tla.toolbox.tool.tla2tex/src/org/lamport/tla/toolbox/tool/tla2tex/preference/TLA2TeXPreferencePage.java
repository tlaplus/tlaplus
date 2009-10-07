package org.lamport.tla.toolbox.tool.tla2tex.preference;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.lamport.tla.toolbox.tool.tla2tex.TLA2TeXActivator;

/**
 * Preference page for TLA2TeX
 * @author Daniel Ricketts
 * @version $Id$
 */
public class TLA2TeXPreferencePage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage
{

    public TLA2TeXPreferencePage()
    {
        super(GRID);
        setPreferenceStore(TLA2TeXActivator.getDefault().getPreferenceStore());
        setDescription("TLA2TeX Preferences");
    }

    public TLA2TeXPreferencePage(int style)
    {
        super(style);
        // TODO Auto-generated constructor stub
    }

    public TLA2TeXPreferencePage(String title, int style)
    {
        super(title, style);
        // TODO Auto-generated constructor stub
    }

    public TLA2TeXPreferencePage(String title, ImageDescriptor image, int style)
    {
        super(title, image, style);
        // TODO Auto-generated constructor stub
    }

    protected void createFieldEditors()
    {
        addField(new BooleanFieldEditor(ITLA2TeXPreferenceConstants.SHADE_COMMENTS,
                "&Shade comments in TLA2TeX output file", getFieldEditorParent()));
        addField(new BooleanFieldEditor(ITLA2TeXPreferenceConstants.NUMBER_LINES,
                "&Number lines in TLA2TeX output file", getFieldEditorParent()));
        addField(new StringFieldEditor(ITLA2TeXPreferenceConstants.LATEX_COMMAND, "&Specify latex command to be used",
                getFieldEditorParent()));
        addField(new DoubleFieldEditor(ITLA2TeXPreferenceConstants.GRAY_LEVEL, "&Specify gray level between 0 and 1",
                getFieldEditorParent(), 0, 1));
    }

    public void init(IWorkbench workbench)
    {
        // TODO Auto-generated method stub

    }

}
