package de.techjava.tla.ui.preferences;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import de.techjava.tla.ui.UIPlugin;

/**
 * TLA Preferences
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLAEditorPreferencePage.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public class TLAEditorPreferencePage 
	extends PreferencePage
	implements IWorkbenchPreferencePage 
{
    public TLAEditorPreferencePage()
    {
		setDescription("TLA+ Editor Preferences");
    }
    /**
     * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
     */
    public void init(IWorkbench workbench) 
    {
		setPreferenceStore(UIPlugin.getDefault().getPreferenceStore());
    }
    
	/**
	 * Initialize default values
	 * @param store
	 */
	public static void initDefaults(IPreferenceStore store)
	{
	}
    /**
     * @see org.eclipse.jface.preference.PreferencePage#createContents(org.eclipse.swt.widgets.Composite)
     */
    protected Control createContents(Composite parent) 
    {
        Composite mainComposite = new Composite(parent, SWT.FILL);
        
        return mainComposite;
    }
    

}

/*
 * $Log: TLAEditorPreferencePage.java,v $
 * Revision 1.1  2005/08/22 15:43:31  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:11  sza
 * additions
 *
 * Revision 1.1  2004/10/06 01:02:29  sza
 * initial commit
 *
 * Revision 1.1  2004/10/06 00:59:04  sza
 * initial commit
 *
 *
 */