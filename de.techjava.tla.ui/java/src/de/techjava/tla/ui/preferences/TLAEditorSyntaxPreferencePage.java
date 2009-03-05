package de.techjava.tla.ui.preferences;

import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.util.ITLAEditorColorConstants;

/**
 * TLA Editor syntax highlightning page
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLAEditorSyntaxPreferencePage.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public class TLAEditorSyntaxPreferencePage
	extends FieldEditorPreferencePage
	implements IWorkbenchPreferencePage 
{
	/**
	 * Default constructor
	 */
	public TLAEditorSyntaxPreferencePage() 
	{
		super(GRID);
		setPreferenceStore(UIPlugin.getDefault().getPreferenceStore());
		setDescription("TLA+ Editor Syntax");
	}
	
	/**
	 * Create field editors
	 * @see org.eclipse.jface.preference.FieldEditorPreferencePage#createFieldEditors()
	 */
	public void createFieldEditors() {
		
	    addField(new ColorFieldEditor(ITLAEditorColorConstants.COMMENT_MULTILINE,	"&Multiline Comment Color:",getFieldEditorParent()));
		addField(new ColorFieldEditor(ITLAEditorColorConstants.COMMENT,				"&Comment Color:",getFieldEditorParent()));
		addField(new ColorFieldEditor(ITLAEditorColorConstants.RESERVED,			"&Reserved Word Color:",getFieldEditorParent()));
		addField(new ColorFieldEditor(ITLAEditorColorConstants.TEXT,				"&Normal Text Color:",getFieldEditorParent()));
		addField(new ColorFieldEditor(ITLAEditorColorConstants.OPERATOR,			"&Operator Color:",getFieldEditorParent()));
		addField(new ColorFieldEditor(ITLAEditorColorConstants.IDENTIFIER,			"&Identifier Color:",getFieldEditorParent()));
	}
	
	public void init(IWorkbench workbench) 
	{
	}
    /**
     * @see org.eclipse.jface.preference.IPreferencePage#performOk()
     */
    public boolean performOk() 
    {
        UIPlugin.getDefault().getColorManager().reInitialize();
        return super.performOk();
    }
    /**
     * @see org.eclipse.jface.preference.PreferencePage#performApply()
     */
    protected void performApply() 
    {
        UIPlugin.getDefault().getColorManager().reInitialize();
        super.performApply();
    }
}